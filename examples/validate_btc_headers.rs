use std::io::{self, BufRead};
use std::time::Instant;
use std::{fs::File, path::Path};

use arecibo::provider::{Bn256EngineKZG, GrumpkinEngine};
use arecibo::traits::circuit::TrivialCircuit;
use arecibo::traits::snark::RelaxedR1CSSNARKTrait;
use arecibo::traits::Engine;
use arecibo::{CompressedSNARK, PublicParams, RecursiveSNARK};
use btc_nova_lc::btc_header::BitcoinHeaderCircuit;
use clap::{Arg, Command};
use ff::Field;
use halo2curves::bn256::{Bn256, G1};
use humansize::{format_size, BINARY};
use humantime::format_duration;
use num_bigint::BigUint;

// Code from https://doc.rust-lang.org/rust-by-example/std_misc/file/read_lines.html
fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

type E1 = Bn256EngineKZG;
type E2 = GrumpkinEngine;
type EE1 = arecibo::provider::hyperkzg::EvaluationEngine<Bn256, E1>;
type EE2 = arecibo::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = arecibo::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = arecibo::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

fn main() {
    let cmd = Command::new("Nova-based Bitcoin header validation")
        .bin_name("validate_btc_headers")
        .arg(
            Arg::new("headers_file")
                .value_name("Bitcoin headers filename")
                .required(true)
                .long_help(
                    "The name of the file containing a list of Bitcoin headers. \
            The file should have one header per line, with the header represented as \
            160 hexadecimal digits.",
                ),
        )
        .arg(
            Arg::new("num_headers")
                .value_name("Number of headers to process")
                .value_parser(clap::value_parser!(u32))
                .required(false)
                .default_value("1")
                .long_help("The number of Bitcoin headers to validate"),
        )
        .after_help("TODO");

    let m = cmd.get_matches();
    let headers_filename = m.get_one::<String>("headers_file").unwrap();
    let num_headers = *m.get_one::<u32>("num_headers").unwrap() as usize;

    let mut headers_vec = vec![];

    // Measure time required to read bitcoin headers from file
    let start = Instant::now();

    if let Ok(lines) = read_lines(headers_filename) {
        let mut num_headers_read = 0usize;

        for line in lines {
            if num_headers_read >= num_headers {
                break;
            }
            if let Ok(hdr_hex_string) = line {
                let header_bytes = hex::decode(hdr_hex_string).expect(&format!(
                    "Failed to read header at height {num_headers_read}"
                ));
                assert_eq!(header_bytes.len(), 80);
                headers_vec.push(header_bytes);
            } else {
                panic!()
            }

            num_headers_read += 1;
        }
    }

    println!(
        "Took {:?} to read {} Bitcoin headers",
        start.elapsed(),
        num_headers
    );

    let circuit_primary = BitcoinHeaderCircuit::<G1>::default();
    let circuit_secondary = TrivialCircuit::default();

    // produce public parameters
    let start = Instant::now();
    println!("Producing public parameters...");
    let pp = PublicParams::<E1>::setup(
        &circuit_primary,
        &circuit_secondary,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    )
    .unwrap();
    let param_gen_time = start.elapsed();
    println!("PublicParams::setup, took {:?} ", param_gen_time);
    let pp_serialized = bincode::serialize(&pp).unwrap();
    let pp_len = format_size(pp_serialized.len(), BINARY);
    println!("PublicParams::size {pp_len}");

    println!(
        "Number of constraints per step (primary circuit): {}",
        pp.num_constraints().0
    );
    println!(
        "Number of constraints per step (secondary circuit): {}",
        pp.num_constraints().1
    );

    println!(
        "Number of variables per step (primary circuit): {}",
        pp.num_variables().0
    );
    println!(
        "Number of variables per step (secondary circuit): {}",
        pp.num_variables().1
    );

    let circuits = headers_vec
        .into_iter()
        .map(|v| BitcoinHeaderCircuit::<<E1 as Engine>::GE>::from_bytes(v))
        .collect::<Vec<_>>();

    let proof_gen_timer = Instant::now();
    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK with {num_headers} Bitcoin headers validated...");
    let z0_primary = BitcoinHeaderCircuit::<<E1 as Engine>::GE>::initial_step_function_inputs();
    let z0_secondary = vec![<E2 as Engine>::Scalar::zero()];

    let mut recursive_snark: RecursiveSNARK<E1> = RecursiveSNARK::<E1>::new(
        &pp,
        &circuits[0],
        &circuit_secondary,
        &z0_primary,
        &z0_secondary,
    )
    .unwrap();

    let start = Instant::now();
    for (i, circuit_primary) in circuits.iter().enumerate() {
        let step_start = Instant::now();
        let res = recursive_snark.prove_step(&pp, circuit_primary, &circuit_secondary);
        assert!(res.is_ok());

        println!(
            "RecursiveSNARK::prove {} : took {:?} ",
            i,
            step_start.elapsed()
        );
    }

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let res = recursive_snark.verify(&pp, num_headers, &z0_primary, &z0_secondary);
    println!("RecursiveSNARK::verify: {:?}", res.is_ok(),);
    assert!(res.is_ok());

    let recursive_snark_proving_time = start.elapsed();
    println!(
        "Total time taken by RecursiveSNARK::prove_steps: {:?}",
        recursive_snark_proving_time
    );

    let start = Instant::now();
    // produce a compressed SNARK
    println!("Generating a CompressedSNARK using Spartan with HyperKZG...");
    let (pk, vk) = CompressedSNARK::<_, S1, S2>::setup(&pp).unwrap();

    let res = CompressedSNARK::<_, S1, S2>::prove(&pp, &pk, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark_proving_time = start.elapsed();
    let proving_time = proof_gen_timer.elapsed();
    println!(
        "CompressedSNARK::prove took {:?}",
        compressed_snark_proving_time,
    );
    let proving_time_human = format_duration(proving_time).to_string();
    println!("Total proving time is {proving_time_human}");

    let compressed_snark = res.unwrap();
    let compressed_snark_serialized = bincode::serialize(&compressed_snark).unwrap();
    let proof_size = format_size(compressed_snark_serialized.len(), BINARY);
    println!("CompressedSNARK::proof_size {proof_size}");

    // verify the compressed SNARK
    println!("Verifying a CompressedSNARK...");
    let start = Instant::now();
    let res = compressed_snark.verify(&vk, num_headers, &z0_primary, &z0_secondary);
    assert!(res.is_ok());

    let verification_time = start.elapsed();
    println!("CompressedSNARK::verify took {:?}", verification_time);

    println!("=========================================================");
    println!("The below line is in CSV format for performance comparison");
    println!(
        "arecibo,{},{:?},{:?},{:?},{:?},{},{},{:?}",
        num_headers,
        proving_time,
        compressed_snark_proving_time,
        recursive_snark_proving_time,
        verification_time,
        compressed_snark_serialized.len(),
        pp_len,
        param_gen_time,
    );
    println!("Fields: num_steps,prove_time,compressed_snark_prove_time,recursive_snark_prove_time,verify_time,proof_size,pp_size,pp_gen_time");
    println!("=========================================================");

    let zn_primary = res.unwrap().0;
    let final_block_height = zn_primary[0] - <E1 as Engine>::Scalar::ONE;
    let final_block_hash = zn_primary[1];
    let accumulated_chainwork = zn_primary[2];
    let pow_threshold = zn_primary[3];

    let mut block_height_str = format!("{:?}", final_block_height);
    block_height_str.remove(0);
    block_height_str.remove(0);
    println!(
        "Verified upto height   {}",
        BigUint::from_bytes_be(&hex::decode(block_height_str).unwrap())
    );
    println!("Latest block hash      {:?}", final_block_hash);
    println!("PoW threshold in block {:?}", pow_threshold);
    println!("Accumulated chainwork  {:?}", accumulated_chainwork);
}
