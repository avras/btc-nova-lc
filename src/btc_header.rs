use bellpepper::gadgets::sha256::sha256;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::Field;
use nova_snark::traits::{circuit::StepCircuit, Group};
use std::marker::PhantomData;

use crate::{
    target::{accumulate_chainwork, calc_new_target, nbits_to_target},
    utils::{
        alloc_constant, alloc_num_equals, conditionally_select, le_bytes_to_alloc_num,
        less_than_or_equal,
    },
};

const HEADER_LENGTH_BITS: usize = 640;
const HEADER_LENGTH_BYTES: usize = 80;
const STEP_FUNCTION_ARITY: usize = 16;
const NUM_BLOCKS_IN_EPOCH: u64 = 2016;
const GENESIS_BLOCK_TIMESTAMP: u64 = 1231006505u64;

#[derive(Clone, Debug)]
pub struct BitcoinHeaderCircuit<G: Group> {
    header: [bool; HEADER_LENGTH_BITS],
    marker: PhantomData<G>,
}

impl<G: Group> Default for BitcoinHeaderCircuit<G> {
    fn default() -> Self {
        Self {
            header: [false; HEADER_LENGTH_BITS],
            marker: Default::default(),
        }
    }
}

impl<G: Group> BitcoinHeaderCircuit<G> {
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        assert_eq!(bytes.len(), HEADER_LENGTH_BYTES);

        let header_bits = bytes
            .iter()
            .flat_map(|b| {
                (0..8)
                    .rev()
                    .map(|i| b & (1 << i) == (1 << i))
                    .collect::<Vec<bool>>()
            })
            .collect::<Vec<bool>>();

        Self {
            header: header_bits.try_into().unwrap(),
            marker: PhantomData,
        }
    }

    pub fn initial_step_function_inputs() -> Vec<G::Scalar> {
        let mut inputs = vec![];
        inputs.push(G::Scalar::ZERO); // Block height modulo 2016
        inputs.push(G::Scalar::ZERO); // Previous block hash (for the genesis block it is defined as all zeros)
        inputs.push(G::Scalar::ZERO); // Accumulated chain work
        inputs.push(G::Scalar::ZERO); // Previous block target (for the genesis block it is not defined)
        inputs.push(G::Scalar::from(GENESIS_BLOCK_TIMESTAMP)); // Epoch start timestamp (value is block 0's timestamp)
        inputs.push(G::Scalar::from(GENESIS_BLOCK_TIMESTAMP)); // Previous block timestamp. We set it to the genesis block
                                                               // timestamp to make it at least as large as the epoch start timestamp
        inputs.extend_from_slice(&[G::Scalar::ZERO; 10]); // Timestamps of 10 previous block (most recent block first)

        assert_eq!(inputs.len(), STEP_FUNCTION_ARITY);
        inputs
    }
}

impl<G: Group> StepCircuit<G::Scalar> for BitcoinHeaderCircuit<G> {
    fn arity(&self) -> usize {
        STEP_FUNCTION_ARITY
    }

    fn synthesize<CS>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<G::Scalar>],
    ) -> Result<Vec<AllocatedNum<G::Scalar>>, SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
        let header_bits: Vec<Boolean> = self
            .header
            .into_iter()
            .enumerate()
            .map(|(i, b)| -> Result<Boolean, SynthesisError> {
                Ok(Boolean::from(AllocatedBit::alloc(
                    cs.namespace(|| format!("alloc bit {i}")),
                    Some(b),
                )?))
            })
            .collect::<Result<Vec<_>, SynthesisError>>()?;

        let prev_block_hash_in_hdr = le_bytes_to_alloc_num(
            cs.namespace(|| "alloc previous block hash"),
            &header_bits[32..256].to_vec(),
        )?;
        let prev_block_hash_correct = alloc_num_equals(
            cs.namespace(|| "prev block hash == header field"),
            &prev_block_hash_in_hdr,
            &z[1],
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| "check prev block correctness"),
            &prev_block_hash_correct,
            &Boolean::Constant(true),
        )?;

        let single_hash = sha256(cs.namespace(|| "hash header once"), &header_bits)?;
        let double_hash = sha256(cs.namespace(|| "hash header twice"), &single_hash)?;

        let (ls_bits, ms_bits) = double_hash.split_at(224);

        for i in 0..ms_bits.len() {
            Boolean::enforce_equal(
                cs.namespace(|| format!("check MS bit {i} in double hash is false")),
                &ms_bits[i],
                &Boolean::Constant(false),
            )?;
        }

        let header_hash = le_bytes_to_alloc_num(
            cs.namespace(|| "alloc hash as field element"),
            &ls_bits.to_vec(),
        )?;

        let (target, mask) = nbits_to_target(
            cs.namespace(|| "get target threshold and mask"),
            &header_bits[576..608].to_vec(),
        )?;

        let header_hash_lte_target = less_than_or_equal(
            cs.namespace(|| "is hash <= target"),
            &header_hash,
            &target,
            224,
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| "enforce hash <= target is true"),
            &header_hash_lte_target,
            &Boolean::Constant(true),
        )?;

        let height_mod_2016 = &z[0];
        let num_blocks_in_epoch = alloc_constant(
            cs.namespace(|| "alloc 2016"),
            G::Scalar::from(NUM_BLOCKS_IN_EPOCH),
        )?;
        let blk_height_2016_multiple = alloc_num_equals(
            cs.namespace(|| "is block height a multiple of 2016"),
            &height_mod_2016,
            &num_blocks_in_epoch,
        )?;

        let one = alloc_constant(cs.namespace(|| "alloc 1"), G::Scalar::ONE)?;
        let height_mod_2016_plus_one =
            height_mod_2016.add(cs.namespace(|| "increment height mod 2016"), &one)?;

        let next_height_mod_2016 = conditionally_select(
            cs.namespace(|| "choose between h+1 and 1"),
            &one,
            &height_mod_2016_plus_one,
            &blk_height_2016_multiple,
        )?;

        let chain_work =
            accumulate_chainwork(cs.namespace(|| "accumulate chainwork"), &z[2], &target)?;

        let current_timestamp = le_bytes_to_alloc_num(
            cs.namespace(|| "alloc current block timestamp"),
            &header_bits[544..576].to_vec(),
        )?;

        let prev_block_target = &z[3];
        let current_epoch_start_timestamp = &z[4];
        let prev_block_timestamp = &z[5];

        let calculated_target = calc_new_target(
            cs.namespace(|| "calculate new target"),
            prev_block_target,
            current_epoch_start_timestamp,
            &prev_block_timestamp,
        )?;
        let unmasked_target = conditionally_select(
            cs.namespace(|| "select new target if block height is a multiple of 2016"),
            &calculated_target,
            prev_block_target,
            &blk_height_2016_multiple,
        )?;

        let target_bits = target.to_bits_le(cs.namespace(|| "get expected target bits"))?;
        let mask_bits = mask.to_bits_le(cs.namespace(|| "get mask bits"))?;
        let unmasked_target_bits =
            unmasked_target.to_bits_le(cs.namespace(|| "get unmasked target bits"))?;

        let mut all_bits_equal = Boolean::Constant(true);
        for i in 0..mask_bits.len() {
            let masked_calculated_target_bit = Boolean::and(
                cs.namespace(|| format!("mask {i} AND calc target bit {i}")),
                &mask_bits[i],
                &unmasked_target_bits[i],
            )?;
            let bits_equal = Boolean::xor(
                cs.namespace(|| format!("target bit XOR calculated target bit {i}")),
                &masked_calculated_target_bit,
                &target_bits[i],
            )?
            .not(); // Note the not()
            all_bits_equal = Boolean::and(
                cs.namespace(|| format!("mask {i} AND {i}")),
                &all_bits_equal,
                &bits_equal,
            )?;
        }

        let all_bits_equal_or_no_update = Boolean::or(
            cs.namespace(|| format!("Either all masked bits match OR block height % 2016 != 0")),
            &all_bits_equal,
            &blk_height_2016_multiple.not(),
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| "Enforce target update is correct"),
            &all_bits_equal_or_no_update,
            &Boolean::Constant(true),
        )?;

        let epoch_start_timestamp = conditionally_select(
            cs.namespace(|| "update epoch start timestamp"),
            &current_timestamp,
            current_epoch_start_timestamp,
            &blk_height_2016_multiple,
        )?;

        let mut z_out = vec![
            next_height_mod_2016,
            header_hash,
            chain_work,
            target,
            epoch_start_timestamp,
            current_timestamp,
        ];
        z_out.extend_from_slice(&z[5..(STEP_FUNCTION_ARITY - 1)]);

        Ok(z_out)
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::target_scalar_from_u32;

    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::PrimeField;
    use nova_snark::{provider::VestaEngine, traits::Engine};
    use pasta_curves::Fp;

    fn le_bytes_to_scalar(bytes: &Vec<u8>) -> Fp {
        assert!(bytes.len() * 8 < Fp::CAPACITY as usize);

        let mut scalar = Fp::ZERO;
        let base = Fp::from(256u64);
        let mut coeff = Fp::ONE;

        for i in 0..bytes.len() {
            scalar += Fp::from(bytes[i] as u64) * coeff;
            coeff = coeff * base;
        }
        scalar
    }

    #[test]
    fn test_genesis_block() {
        let header_0 = "01000000000000000000000000000000\
                              00000000000000000000000000000000\
                              000000003ba3edfd7a7b12b27ac72c3e\
                              67768f617fc81bc3888a51323a9fb8aa\
                              4b1e5e4a29ab5f49ffff001d1dac2b7c";
        let header_1 = "010000006fe28c0ab6f1b372c1a6a246\
                              ae63f74f931e8365e15a089c68d61900\
                              00000000982051fd1e4ba744bbbe680e\
                              1fee14677ba1a3c3540bf7b1cdb606e8\
                              57233e0e61bc6649ffff001d01e36299";

        let header_0_bytes = hex::decode(header_0).unwrap();
        type G1 = <VestaEngine as Engine>::GE;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let z_in_values = BitcoinHeaderCircuit::<G1>::initial_step_function_inputs();

        let z_in = z_in_values
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || v)
            })
            .collect::<Vec<_>>();

        let header_circuit = BitcoinHeaderCircuit::<G1>::from_bytes(header_0_bytes.clone());
        let res = header_circuit.synthesize(&mut cs.namespace(|| "verify header"), &z_in);
        assert!(res.is_ok());
        let z_out = res.unwrap();
        assert_eq!(z_out[0].get_value().unwrap(), Fp::ONE);

        let header_1_bytes = hex::decode(header_1).unwrap();
        let hash_val = le_bytes_to_scalar(&header_1_bytes[4..32].to_vec());
        assert_eq!(z_out[1].get_value().unwrap(), hash_val);

        assert_eq!(z_out[2].get_value().unwrap(), Fp::from(0x100010001u64));

        let target_scalar = target_scalar_from_u32::<Fp>(u32::from_le_bytes(
            header_0_bytes[72..76].try_into().unwrap(),
        ));
        assert_eq!(z_out[3].get_value().unwrap(), target_scalar);
        assert_eq!(z_out[4].get_value().unwrap(), z_in_values[4]);

        let timestamp_scalar =
            Fp::from(u32::from_le_bytes(header_0_bytes[68..72].try_into().unwrap()) as u64);

        assert_eq!(z_out[5].get_value().unwrap(), timestamp_scalar);
        // We set the previous block timestamp to genesis block timestamp
        assert_eq!(z_out[6].get_value().unwrap(), timestamp_scalar);
        for i in 7..STEP_FUNCTION_ARITY - 1 {
            assert_eq!(
                z_out[i].get_value().unwrap(),
                z_in[i - 1].get_value().unwrap()
            );
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 93394);
    }

    #[test]
    fn test_block_one() {
        let header_0 = "01000000000000000000000000000000\
                              00000000000000000000000000000000\
                              000000003ba3edfd7a7b12b27ac72c3e\
                              67768f617fc81bc3888a51323a9fb8aa\
                              4b1e5e4a29ab5f49ffff001d1dac2b7c";
        let header_1 = "010000006fe28c0ab6f1b372c1a6a246\
                              ae63f74f931e8365e15a089c68d61900\
                              00000000982051fd1e4ba744bbbe680e\
                              1fee14677ba1a3c3540bf7b1cdb606e8\
                              57233e0e61bc6649ffff001d01e36299";
        let header_2 = "010000004860eb18bf1b1620e37e9490\
                              fc8a427514416fd75159ab86688e9a83\
                              00000000d5fdcc541e25de1c7a5added\
                              f24858b8bb665c9f36ef744ee42c3160\
                              22c90f9bb0bc6649ffff001d08d2bd61";

        let header_0_bytes = hex::decode(header_0).unwrap();
        let header_1_bytes = hex::decode(header_1).unwrap();
        let header_2_bytes = hex::decode(header_2).unwrap();
        type G1 = <VestaEngine as Engine>::GE;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut z_in_values = vec![];
        z_in_values.push(Fp::ONE); // Block height modulo 2016
        z_in_values.push(le_bytes_to_scalar(&header_1_bytes[4..32].to_vec())); // Previous block hash
        z_in_values.push(Fp::from(0x100010001u64)); // Accumulated chain work
        z_in_values.push(target_scalar_from_u32(0x1D00FFFF)); // Previous block target
        z_in_values.push(Fp::from(GENESIS_BLOCK_TIMESTAMP)); // Epoch start timestamp
        z_in_values.push(Fp::from(GENESIS_BLOCK_TIMESTAMP)); // Previous block timestamp
                                                             // We set the timestamp before the genesis block to the same value as the genesis block
                                                             // timestamp (to satisfy non-negative constraint on the difference between previous block
                                                             // timestamp and epoch start time)
        z_in_values.push(Fp::from(GENESIS_BLOCK_TIMESTAMP));
        z_in_values.extend_from_slice(&[Fp::ZERO; 9]); // Timestamps of 9 previous block (most recent block first)

        let z_in = z_in_values
            .clone()
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                AllocatedNum::alloc_infallible(cs.namespace(|| format!("alloc z_in[{i}]")), || v)
            })
            .collect::<Vec<_>>();

        let header_circuit = BitcoinHeaderCircuit::<G1>::from_bytes(header_1_bytes.clone());
        let res = header_circuit.synthesize(&mut cs.namespace(|| "verify header"), &z_in);
        assert!(res.is_ok());
        let z_out = res.unwrap();
        assert_eq!(z_out[0].get_value().unwrap(), Fp::from(2u64));

        let hash_val = le_bytes_to_scalar(&header_2_bytes[4..32].to_vec());
        assert_eq!(z_out[1].get_value().unwrap(), hash_val);

        assert_eq!(z_out[2].get_value().unwrap(), Fp::from(0x200020002u64));

        let target_scalar = target_scalar_from_u32::<Fp>(u32::from_le_bytes(
            header_1_bytes[72..76].try_into().unwrap(),
        ));
        assert_eq!(z_out[3].get_value().unwrap(), target_scalar);
        assert_eq!(z_out[4].get_value().unwrap(), z_in_values[4]);

        let block0_timestamp_scalar =
            Fp::from(u32::from_le_bytes(header_0_bytes[68..72].try_into().unwrap()) as u64);
        let block1_timestamp_scalar =
            Fp::from(u32::from_le_bytes(header_1_bytes[68..72].try_into().unwrap()) as u64);

        assert_eq!(z_out[5].get_value().unwrap(), block1_timestamp_scalar);
        assert_eq!(z_out[6].get_value().unwrap(), block0_timestamp_scalar);
        for i in 7..STEP_FUNCTION_ARITY - 1 {
            assert_eq!(
                z_out[i].get_value().unwrap(),
                z_in[i - 1].get_value().unwrap()
            );
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 93394);
    }
}
