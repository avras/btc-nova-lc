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
    target::nbits_to_target,
    utils::{le_bytes_to_alloc_num, less_than_or_equal},
};

const HEADER_LENGTH_BITS: usize = 640;
const HEADER_LENGTH_BYTES: usize = 80;
const STEP_FUNCTION_ARITY: usize = 16;

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
        inputs.push(G::Scalar::ZERO); // Previous block hash (for block 0 it is defined as all zeros)
        inputs.push(G::Scalar::ZERO); // Previous block target (for block 0 it is not defined)
        inputs.push(G::Scalar::ZERO); // Accumulated chain work
        inputs.push(G::Scalar::from(1231006505u64)); // Epoch start timestamp (value is block 0's timestamp)
        inputs.extend_from_slice(&[G::Scalar::ZERO; 11]); // Timestamps of 11 previous block timestamp (most recent block first)

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

        Ok(z.to_vec())
    }
}
