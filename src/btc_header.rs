use bellpepper::gadgets::sha256::sha256;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::{Field, PrimeFieldBits};
use nova_snark::traits::{circuit::StepCircuit, Group};
use std::marker::PhantomData;

use crate::{
    median::{compute_median_timestamp, NUM_TIMESTAMP_BITS},
    target::{accumulate_chainwork, calc_new_target, nbits_to_target},
    utils::{
        alloc_constant, alloc_num_equals, alloc_num_equals_constant, conditionally_select,
        le_bytes_to_alloc_num, less_than, less_than_or_equal, range_check_num,
    },
};

const HEADER_LENGTH_BITS: usize = 640;
const HEADER_LENGTH_BYTES: usize = 80;
const STEP_FUNCTION_ARITY: usize = 16;
const NUM_BLOCKS_IN_EPOCH: u64 = 2016;

fn height_modulo_2016<Scalar, CS>(
    mut cs: CS,
    height: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let val_2016 = Scalar::from(NUM_BLOCKS_IN_EPOCH);
    let num_blocks_in_epoch = alloc_constant(cs.namespace(|| "alloc 2016"), val_2016)?;

    // Will work as long as height < 16,777,216
    range_check_num(
        cs.namespace(|| "check that height fits in 24 bits"),
        &height,
        24,
    )?;

    let height_u64 = height.get_value().map(|h| {
        let mut h_val = 0u64;
        let mut coeff = 1u64;
        let h_bits = h.to_le_bits();
        for i in 0..24 {
            if h_bits[i] {
                h_val += coeff;
            }
            coeff = 2 * coeff;
        }
        h_val
    });

    let quotient_u64 = height_u64.map(|h| h / NUM_BLOCKS_IN_EPOCH);
    let remainder_u64 = height_u64.map(|h| h % NUM_BLOCKS_IN_EPOCH);
    let quotient_scalar = quotient_u64.map(Scalar::from);
    let remainder_scalar = remainder_u64.map(Scalar::from);

    let quotient = AllocatedNum::alloc(cs.namespace(|| "alloc quotient"), || {
        quotient_scalar.ok_or(SynthesisError::AssignmentMissing)
    })?;
    let remainder = AllocatedNum::alloc(cs.namespace(|| "alloc remainder"), || {
        remainder_scalar.ok_or(SynthesisError::AssignmentMissing)
    })?;

    // height fits in 24 bits and 2016 fits in 11 bits. So quotient fits in 13 bits
    range_check_num(
        cs.namespace(|| "check that quotient fits in 13 bits"),
        &quotient,
        13,
    )?;
    range_check_num(
        cs.namespace(|| "check that remainder fits in 11 bits"),
        &remainder,
        11,
    )?;

    let rem_lt_2016 = less_than(
        cs.namespace(|| "check remainder < 2016"),
        &remainder,
        &num_blocks_in_epoch,
        11,
    )?;
    Boolean::enforce_equal(
        cs.namespace(|| "remainder < 2016 == true"),
        &rem_lt_2016,
        &Boolean::Constant(true),
    )?;

    cs.enforce(
        || "quotient * 2016 + remainder == height",
        |lc| lc + (val_2016, quotient.get_variable()) + remainder.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + height.get_variable(),
    );

    Ok(remainder)
}

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
    /// Creates an instance from 80 bytes. The `header` field has 640 bools.
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

    /// Generates the initial inputs to the Nova step function
    pub fn initial_step_function_inputs() -> Vec<G::Scalar> {
        let z = vec![G::Scalar::ZERO; STEP_FUNCTION_ARITY];
        // z[0]  Block height
        // z[1]  Previous block hash (for the genesis block it is defined as all zeros)
        // z[2]  Accumulated chain work
        // z[3]  Previous block target (for the genesis block it is not defined)
        // z[4]  Epoch start timestamp (for the genesis block it is not defined)
        // z[5..16] Timestamps of 11 previous block (most recent block first)
        z
    }

    /// Increments the block height and returns updated value
    pub fn increment_height<CS>(
        mut cs: CS,
        height: &AllocatedNum<G::Scalar>,
    ) -> Result<AllocatedNum<G::Scalar>, SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
        let height_plus_one = AllocatedNum::alloc(cs.namespace(|| "alloc height+1"), || {
            height
                .get_value()
                .map(|h| h + G::Scalar::ONE)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
            || "check updated height",
            |lc| lc + height.get_variable() + CS::one(),
            |lc| lc + CS::one(),
            |lc| lc + height_plus_one.get_variable(),
        );

        Ok(height_plus_one)
    }

    /// Increments the block height and returns updated value
    pub fn verify_prev_block_hash<CS>(
        mut cs: CS,
        header_bits: &Vec<Boolean>,
        prev_block_hash: &AllocatedNum<G::Scalar>,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
        let prev_block_hash_in_hdr = le_bytes_to_alloc_num(
            cs.namespace(|| "alloc previous block hash"),
            &header_bits[32..256].to_vec(),
        )?;
        let prev_block_hash_correct = alloc_num_equals(
            cs.namespace(|| "prev block hash == header field"),
            &prev_block_hash_in_hdr,
            prev_block_hash,
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| "check prev block correctness"),
            &prev_block_hash_correct,
            &Boolean::Constant(true),
        )
    }

    /// Verifices that the double SHA256 hash of the block header falls
    /// below the target threshold. Returns the header hash as a field element.
    /// As hash always has at least 32 leading zero bits, it fits in a field
    /// element as long as the field can represent 224-bit integers
    pub fn verify_proof_of_work<CS>(
        mut cs: CS,
        header_bits: &Vec<Boolean>,
        target: &AllocatedNum<G::Scalar>,
    ) -> Result<AllocatedNum<G::Scalar>, SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
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

        Ok(header_hash)
    }

    /// Verifies that the target in the current header has been updated
    /// correctly if the block height is a multiple of 2016. Returns the
    /// updated epoch start timestamp (the current block's timestamp in case
    /// block height is a multiple of 2016)
    pub fn verify_target<CS>(
        mut cs: CS,
        height: &AllocatedNum<G::Scalar>,
        current_timestamp: &AllocatedNum<G::Scalar>,
        target: &AllocatedNum<G::Scalar>,
        prev_block_target: &AllocatedNum<G::Scalar>,
        current_epoch_start_timestamp: &AllocatedNum<G::Scalar>,
        prev_block_timestamp: &AllocatedNum<G::Scalar>,
        mask: &AllocatedNum<G::Scalar>,
    ) -> Result<AllocatedNum<G::Scalar>, SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
        let is_genesis_block =
            alloc_num_equals_constant(cs.namespace(|| "is height == 0"), height, G::Scalar::ZERO)?;

        let height_mod_2016 = height_modulo_2016(cs.namespace(|| "alloc height mod 2016"), height)?;
        let blk_height_2016_multiple = alloc_num_equals_constant(
            cs.namespace(|| "is block height a multiple of 2016"),
            &height_mod_2016,
            G::Scalar::ZERO,
        )?;

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

        let no_target_update = Boolean::or(
            cs.namespace(|| "either height == 0 or height mod 2016 != 0"),
            &is_genesis_block,
            &blk_height_2016_multiple.not(),
        )?;
        let all_bits_equal_or_no_update = Boolean::or(
            cs.namespace(|| format!("Either all masked bits match OR block height % 2016 != 0")),
            &all_bits_equal,
            &no_target_update,
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

        Ok(epoch_start_timestamp)
    }

    /// Verifies that the current timestamp is at least as large
    /// as the median of the previous 11 block timestamps
    pub fn verify_current_timestamp<CS>(
        mut cs: CS,
        current_timestamp: &AllocatedNum<G::Scalar>,
        prev_timestamps: &Vec<AllocatedNum<G::Scalar>>,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
        let median_timestamp =
            compute_median_timestamp(cs.namespace(|| "compute median timestamp"), prev_timestamps)?;

        let is_median_lte_current_ts = less_than_or_equal(
            cs.namespace(|| "is current timestamp >= median timestamp"),
            &median_timestamp,
            current_timestamp,
            NUM_TIMESTAMP_BITS,
        )?;

        Boolean::enforce_equal(
            cs.namespace(|| "check inequality holds"),
            &is_median_lte_current_ts,
            &Boolean::Constant(true),
        )
    }

    /// Verifies a single Bitcoin block header
    pub fn verify_btc_header<CS>(
        &self,
        mut cs: CS,
        z: &[AllocatedNum<G::Scalar>],
    ) -> Result<Vec<AllocatedNum<G::Scalar>>, SynthesisError>
    where
        CS: ConstraintSystem<G::Scalar>,
    {
        let height = &z[0];
        let prev_block_hash = &z[1];
        let old_chainwork = &z[2];
        let prev_block_target = &z[3];
        let current_epoch_start_timestamp = &z[4];
        let prev_block_timestamp = &z[5];
        let prev_eleven_block_timestamps = z[5..].to_vec();

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

        let height_plus_one = Self::increment_height(cs.namespace(|| "increment height"), height)?;

        Self::verify_prev_block_hash(
            cs.namespace(|| "verify previous block hash"),
            &header_bits,
            prev_block_hash,
        )?;

        let (target, mask) = nbits_to_target(
            cs.namespace(|| "get target threshold and mask"),
            &header_bits[576..608].to_vec(),
        )?;

        let header_hash = Self::verify_proof_of_work(
            cs.namespace(|| "verify proof of work"),
            &header_bits,
            &target,
        )?;

        let current_timestamp = le_bytes_to_alloc_num(
            cs.namespace(|| "alloc current block timestamp"),
            &header_bits[544..576].to_vec(),
        )?;

        let epoch_start_timestamp = Self::verify_target(
            cs.namespace(|| "verify target calculation"),
            height,
            &current_timestamp,
            &target,
            prev_block_target,
            current_epoch_start_timestamp,
            prev_block_timestamp,
            &mask,
        )?;

        Self::verify_current_timestamp(
            cs.namespace(|| "verify current timestamp"),
            &current_timestamp,
            &prev_eleven_block_timestamps,
        )?;

        let chain_work = accumulate_chainwork(
            cs.namespace(|| "accumulate chainwork"),
            old_chainwork,
            &target,
        )?;

        let mut z_out = vec![
            height_plus_one,
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
        self.verify_btc_header(cs.namespace(|| "verify BTC header"), z)
    }
}

#[derive(Clone, Debug)]
pub struct BitcoinMultiHeaderCircuit<G: Group> {
    num_headers_per_step: usize,
    header_circuits: Vec<BitcoinHeaderCircuit<G>>,
}

impl<G: Group> BitcoinMultiHeaderCircuit<G> {
    pub fn new(num_headers_per_step: usize, header_vec: Vec<Vec<u8>>) -> Self {
        assert_eq!(header_vec.len(), num_headers_per_step);

        let header_circuits = header_vec
            .into_iter()
            .map(|hdr_bytes| BitcoinHeaderCircuit::<G>::from_bytes(hdr_bytes))
            .collect::<Vec<_>>();
        Self {
            num_headers_per_step,
            header_circuits,
        }
    }
}

impl<G: Group> StepCircuit<G::Scalar> for BitcoinMultiHeaderCircuit<G> {
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
        let mut z_out = z.to_vec();

        for i in 0..self.num_headers_per_step {
            z_out = self.header_circuits[i]
                .verify_btc_header(cs.namespace(|| format!("verify BTC header {i}")), &z_out)?;
        }

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

    const GENESIS_BLOCK_TIMESTAMP: u64 = 1231006505u64;
    const HEADER_0: &str = "01000000000000000000000000000000\
                            00000000000000000000000000000000\
                            000000003ba3edfd7a7b12b27ac72c3e\
                            67768f617fc81bc3888a51323a9fb8aa\
                            4b1e5e4a29ab5f49ffff001d1dac2b7c";
    const HEADER_1: &str = "010000006fe28c0ab6f1b372c1a6a246\
                            ae63f74f931e8365e15a089c68d61900\
                            00000000982051fd1e4ba744bbbe680e\
                            1fee14677ba1a3c3540bf7b1cdb606e8\
                            57233e0e61bc6649ffff001d01e36299";
    const HEADER_2: &str = "010000004860eb18bf1b1620e37e9490\
                            fc8a427514416fd75159ab86688e9a83\
                            00000000d5fdcc541e25de1c7a5added\
                            f24858b8bb665c9f36ef744ee42c3160\
                            22c90f9bb0bc6649ffff001d08d2bd61";

    #[test]
    fn test_height_mod_2016() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let test_cases = [0u64, 1, 2016, 2017, 4032, 4033];

        for i in 0..test_cases.len() {
            let res = AllocatedNum::alloc(cs.namespace(|| format!("alloc height {i}")), || {
                Ok(Fp::from(test_cases[i]))
            });
            assert!(res.is_ok());
            let height = res.unwrap();

            let res = height_modulo_2016(
                cs.namespace(|| format!("alloc height modulo 2016 {i}")),
                &height,
            );
            assert!(res.is_ok());
            let height_mod_2016 = res.unwrap();

            assert_eq!(
                height_mod_2016.get_value().unwrap(),
                Fp::from(test_cases[i] % NUM_BLOCKS_IN_EPOCH)
            );
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 65 * test_cases.len());
    }

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
        let header_0_bytes = hex::decode(HEADER_0).unwrap();
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

        let header_1_bytes = hex::decode(HEADER_1).unwrap();
        let hash_val = le_bytes_to_scalar(&header_1_bytes[4..32].to_vec());
        assert_eq!(z_out[1].get_value().unwrap(), hash_val);

        assert_eq!(z_out[2].get_value().unwrap(), Fp::from(0x100010001u64));

        let target_scalar = target_scalar_from_u32::<Fp>(u32::from_le_bytes(
            header_0_bytes[72..76].try_into().unwrap(),
        ));
        assert_eq!(z_out[3].get_value().unwrap(), target_scalar);
        assert_eq!(
            z_out[4].get_value().unwrap(),
            Fp::from(GENESIS_BLOCK_TIMESTAMP)
        );

        let timestamp_scalar =
            Fp::from(u32::from_le_bytes(header_0_bytes[68..72].try_into().unwrap()) as u64);

        assert_eq!(z_out[5].get_value().unwrap(), timestamp_scalar);
        assert_eq!(z_out[6].get_value().unwrap(), Fp::ZERO);
        for i in 7..STEP_FUNCTION_ARITY - 1 {
            assert_eq!(
                z_out[i].get_value().unwrap(),
                z_in[i - 1].get_value().unwrap()
            );
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 90598);
    }

    #[test]
    fn test_block_one() {
        let header_0_bytes = hex::decode(HEADER_0).unwrap();
        let header_1_bytes = hex::decode(HEADER_1).unwrap();
        let header_2_bytes = hex::decode(HEADER_2).unwrap();
        type G1 = <VestaEngine as Engine>::GE;

        let mut cs = TestConstraintSystem::<Fp>::new();
        let mut z_in_values = vec![];
        z_in_values.push(Fp::ONE); // Block height modulo 2016
        z_in_values.push(le_bytes_to_scalar(&header_1_bytes[4..32].to_vec())); // Previous block hash
        z_in_values.push(Fp::from(0x100010001u64)); // Accumulated chain work
        z_in_values.push(target_scalar_from_u32(0x1D00FFFF)); // Previous block target
        z_in_values.push(Fp::from(GENESIS_BLOCK_TIMESTAMP)); // Epoch start timestamp
        z_in_values.push(Fp::from(GENESIS_BLOCK_TIMESTAMP)); // Previous block timestamp
        z_in_values.extend_from_slice(&[Fp::ZERO; 10]); // Timestamps of 10 previous block (most recent block first)

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
        assert_eq!(
            z_out[4].get_value().unwrap(),
            Fp::from(GENESIS_BLOCK_TIMESTAMP)
        );

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
        assert_eq!(cs.num_constraints(), 90598);
    }

    #[test]
    fn test_two_blocks() {
        let header_0_bytes = hex::decode(HEADER_0).unwrap();
        let header_1_bytes = hex::decode(HEADER_1).unwrap();
        let header_2_bytes = hex::decode(HEADER_2).unwrap();
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

        let header_circuit = BitcoinMultiHeaderCircuit::<G1>::new(
            2,
            vec![header_0_bytes.clone(), header_1_bytes.clone()],
        );
        let res = header_circuit.synthesize(&mut cs.namespace(|| "verify two headers"), &z_in);
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
        assert_eq!(
            z_out[4].get_value().unwrap(),
            Fp::from(GENESIS_BLOCK_TIMESTAMP)
        );

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
        assert_eq!(cs.num_constraints(), 181196);
    }
}
