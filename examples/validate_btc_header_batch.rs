use std::io::{self, BufRead};
use std::time::Instant;
use std::{fs::File, path::Path};

use btc_nova_lc::btc_header::{BitcoinHeaderCircuit, BitcoinMultiHeaderCircuit};
use clap::{Arg, Command};
use nova_snark::provider::{Bn256EngineKZG, GrumpkinEngine};
use nova_snark::traits::circuit::TrivialCircuit;
use nova_snark::traits::snark::RelaxedR1CSSNARKTrait;
use nova_snark::traits::Engine;
use nova_snark::{PublicParams, RecursiveSNARK};

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
type EE1 = nova_snark::provider::hyperkzg::EvaluationEngine<E1>;
type EE2 = nova_snark::provider::ipa_pc::EvaluationEngine<E2>;
type S1 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E1, EE1>; // non-preprocessing SNARK
type S2 = nova_snark::spartan::snark::RelaxedR1CSSNARK<E2, EE2>; // non-preprocessing SNARK

fn main() {
    let cmd = Command::new("Nova-based Bitcoin header batch validation")
        .bin_name("validate_btc_header_batch")
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
            Arg::new("num_headers_per_step")
                .value_name("Number of headers validated in each Nova step")
                .value_parser(clap::value_parser!(u32))
                .required(true)
                .long_help("Number of Bitcoin headers validated in each Nova step"),
        )
        .arg(
            Arg::new("num_steps")
                .value_name("Number of Nova steps")
                .value_parser(clap::value_parser!(u32))
                .required(true)
                .long_help("Number of Nova steps"),
        )
        .after_help("TODO");

    let m = cmd.get_matches();
    let headers_filename = m.get_one::<String>("headers_file").unwrap();
    let num_headers_per_step = *m.get_one::<u32>("num_headers_per_step").unwrap() as usize;
    let num_steps = *m.get_one::<u32>("num_steps").unwrap() as usize;

    let mut headers_vec = vec![];

    // Measure time required to read bitcoin headers from file
    let start = Instant::now();

    if let Ok(lines) = read_lines(headers_filename) {
        let mut num_headers_read = 0usize;

        for line in lines {
            if num_headers_read >= num_headers_per_step * num_steps {
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

    let mut batch_headers_vec = vec![];
    for i in 0..num_steps {
        let mut headers_batch = vec![];
        for j in 0..num_headers_per_step {
            headers_batch.push(headers_vec[i * num_headers_per_step + j].clone());
        }
        batch_headers_vec.push(headers_batch);
    }

    println!(
        "Took {:?} to read {} Bitcoin headers",
        start.elapsed(),
        num_headers_per_step * num_steps
    );

    type C1 = BitcoinMultiHeaderCircuit<<E1 as Engine>::GE>;
    type C2 = TrivialCircuit<<E2 as Engine>::Scalar>;

    assert!(batch_headers_vec.len() > 0);
    let circuit_primary =
        BitcoinMultiHeaderCircuit::new(num_headers_per_step, batch_headers_vec[0].clone());
    let circuit_secondary = TrivialCircuit::default();

    // produce public parameters
    let start = Instant::now();
    println!("Producing public parameters...");
    let pp = PublicParams::<E1, E2, C1, C2>::setup(
        &circuit_primary,
        &circuit_secondary,
        &*S1::ck_floor(),
        &*S2::ck_floor(),
    )
    .unwrap();
    println!("PublicParams::setup, took {:?} ", start.elapsed());

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

    let circuits = batch_headers_vec
        .into_iter()
        .map(|v| BitcoinMultiHeaderCircuit::<<E1 as Engine>::GE>::new(num_headers_per_step, v))
        .collect::<Vec<_>>();

    // produce a recursive SNARK
    println!("Generating a RecursiveSNARK with {num_headers_per_step} Bitcoin headers validated per step...");
    let z0_primary = BitcoinHeaderCircuit::<<E1 as Engine>::GE>::initial_step_function_inputs();

    let mut recursive_snark: RecursiveSNARK<E1, E2, C1, C2> =
        RecursiveSNARK::<E1, E2, C1, C2>::new(
            &pp,
            &circuits[0],
            &circuit_secondary,
            &z0_primary,
            &[<E2 as Engine>::Scalar::zero()],
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
    println!(
        "Total time taken by RecursiveSNARK::prove_steps: {:?}",
        start.elapsed()
    );

    // verify the recursive SNARK
    println!("Verifying a RecursiveSNARK...");
    let res = recursive_snark.verify(
        &pp,
        num_steps,
        &z0_primary,
        &[<E2 as Engine>::Scalar::zero()],
    );
    println!("RecursiveSNARK::verify: {:?}", res.is_ok(),);
    assert!(res.is_ok());
}
