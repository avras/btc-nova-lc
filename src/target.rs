use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::PrimeFieldBits;

use crate::{
    uint256::Uint256,
    utils::{
        alloc_constant, conditionally_select, le_bytes_to_alloc_num, less_than, range_check_num,
    },
};

// The maximum value of the exponent in nbits = 0x1D
// The maximum shift is then 0x1A = 0x1D - 3
const MAX_MANTISSA_SHIFT: u8 = 0x1A;

// Mask to compare calculated target with
// target in header
const MANTISSA_MASK: u64 = 0xFFFFFF;

// Number of seconds in 2 weeks
const EXPECTED_EPOCH_TIMESPAN: u64 = 14 * 24 * 3600;

// Target corresponding to nbits = 0x1D00FFFF
// Decimal form of 0x00FFFF * 256^(0x1D-3) =
const MAX_TARGET_DECIMAL_STR: &str =
    "26959535291011309493156476344723991336010898738574164086137773096960";

pub(crate) fn nbits_to_target<Scalar, CS>(
    mut cs: CS,
    nbits: &Vec<Boolean>,
) -> Result<(AllocatedNum<Scalar>, AllocatedNum<Scalar>), SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(nbits.len(), 32);
    let exponent_bits = &nbits[24..];
    let exponent_value: Option<u8> =
        exponent_bits
            .iter()
            .enumerate()
            .fold(Some(0u8), |acc, (i, b)| match b.get_value() {
                Some(b_val) => {
                    if b_val {
                        acc.map(|a| a + (1u8 << (7 - i)))
                    } else {
                        acc
                    }
                }
                None => None,
            });

    let shift_value = exponent_value.map(|m| m - 3u8);
    let shift_value_bits_be = (0..8)
        .rev()
        .map(|i| shift_value.map(|e| e & (1u8 << i) == (1u8 << i)))
        .collect::<Option<Vec<bool>>>();

    let shift_byte = (0..8)
        .map(|i| -> Result<AllocatedBit, SynthesisError> {
            AllocatedBit::alloc(
                cs.namespace(|| format!("exponent bit {i}")),
                shift_value_bits_be.as_ref().map(|v| v[i]),
            )
        })
        .collect::<Result<Vec<_>, SynthesisError>>()?
        .into_iter()
        .map(Boolean::from)
        .collect::<Vec<_>>();

    let shift = le_bytes_to_alloc_num(cs.namespace(|| "alloc shift"), &shift_byte)?;

    // shift + 3 == exponent
    cs.enforce(
        || "check shift consistency with exponent bits",
        |mut lc| {
            let mut coeff = Scalar::ONE;
            for b in exponent_bits.iter().rev() {
                lc = lc + &b.lc(CS::one(), coeff);
                coeff = coeff.double();
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc + shift.get_variable() + (Scalar::from(3u64), CS::one()),
    );

    let mantissa =
        le_bytes_to_alloc_num(cs.namespace(|| "alloc mantissa"), &nbits[0..24].to_vec())?;

    // An indicator vector of 27 bits which will indicate the shift value
    // Maximum value of exponent is 0x1D = 29. So max shift value is 26.
    let mut shift_indicator_bits: Vec<Boolean> = vec![];
    for i in 0..=MAX_MANTISSA_SHIFT {
        let b = Boolean::from(AllocatedBit::alloc(
            cs.namespace(|| format!("indicator bit {i}")),
            shift_value.map(|s| s == i),
        )?);
        shift_indicator_bits.push(b);
    }

    // Check that the sum of the bits equals one
    cs.enforce(
        || "check that exactly one of the indicator bits is true",
        |mut lc| {
            for b in shift_indicator_bits.iter() {
                lc = lc + &b.lc(CS::one(), Scalar::ONE);
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc + CS::one(),
    );

    cs.enforce(
        || "check that shift value is consistent with indicator bits",
        |mut lc| {
            let mut coeff = Scalar::ZERO;
            for b in shift_indicator_bits.iter() {
                lc = lc + &b.lc(CS::one(), coeff);
                coeff = coeff + Scalar::ONE;
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc + shift.get_variable(),
    );

    let multiplier_scalar = shift_value.and_then(|s| {
        let mut mul = Scalar::ONE;
        let coeff = Scalar::from(256u64);
        for _i in 0..s {
            mul = mul * coeff;
        }
        Some(mul)
    });

    let multiplier = AllocatedNum::alloc(cs.namespace(|| "alloc multiplier"), || {
        multiplier_scalar.ok_or(SynthesisError::AssignmentMissing)
    })?;
    cs.enforce(
        || "check multiplier consistency with shift indicator bits",
        |mut lc| {
            let base = Scalar::from(256u64);
            let mut coeff = Scalar::ONE;
            for b in shift_indicator_bits.iter() {
                lc = lc + &b.lc(CS::one(), coeff);
                coeff = coeff * base;
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc + multiplier.get_variable(),
    );

    let expected_target_scalar = mantissa
        .get_value()
        .and_then(|m| multiplier_scalar.and_then(|mul| Some(m * mul)));

    let expected_target = AllocatedNum::alloc(cs.namespace(|| "alloc expected target"), || {
        expected_target_scalar.ok_or(SynthesisError::AssignmentMissing)
    })?;

    cs.enforce(
        || "check mantissa * multiplier == expected target",
        |lc| lc + mantissa.get_variable(),
        |lc| lc + multiplier.get_variable(),
        |lc| lc + expected_target.get_variable(),
    );

    let unshifted_mask = alloc_constant(cs.namespace(||"alloc unshifted mask"), Scalar::from(MANTISSA_MASK))?;
    let mask = unshifted_mask.mul(cs.namespace(|| "unshifted mask * multiplier"), &multiplier)?;

    Ok((expected_target, mask))
}

pub(crate) fn calc_new_target<Scalar, CS>(
    mut cs: CS,
    old_target: &AllocatedNum<Scalar>,
    epoch_start_time: &AllocatedNum<Scalar>,
    epoch_end_time: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    range_check_num(
        cs.namespace(|| "range check epoch start time"),
        epoch_start_time,
        32,
    )?;
    range_check_num(
        cs.namespace(|| "range check epoch end time"),
        epoch_end_time,
        32,
    )?;

    let epoch_duration_scalar = match (epoch_start_time.get_value(), epoch_end_time.get_value()) {
        (Some(start), Some(end)) => Some(end - start),
        (_, _) => None,
    };
    let epoch_duration = AllocatedNum::alloc(cs.namespace(|| "alloc epoch duration"), || {
        epoch_duration_scalar.ok_or(SynthesisError::AssignmentMissing)
    })?;
    range_check_num(
        cs.namespace(|| "range check epoch duration"),
        &epoch_duration,
        32,
    )?;

    let max_epoch_duration = alloc_constant(
        cs.namespace(|| "alloc max epoch duration"),
        Scalar::from(EXPECTED_EPOCH_TIMESPAN * 4),
    )?;
    let min_epoch_duration = alloc_constant(
        cs.namespace(|| "alloc min epoch duration"),
        Scalar::from(EXPECTED_EPOCH_TIMESPAN / 4),
    )?;

    let epoch_overflow = less_than(
        cs.namespace(|| "is epoch timespan >= max"),
        &max_epoch_duration,
        &epoch_duration,
        32,
    )?;
    let epoch_underflow = less_than(
        cs.namespace(|| "is epoch timespan <= min"),
        &epoch_duration,
        &min_epoch_duration,
        32,
    )?;

    let epoch_duration = conditionally_select(
        cs.namespace(|| "clip overflowing epoch duration"),
        &max_epoch_duration,
        &epoch_duration,
        &epoch_overflow,
    )?;
    let epoch_duration = conditionally_select(
        cs.namespace(|| "clip underflowing epoch duration"),
        &min_epoch_duration,
        &epoch_duration,
        &epoch_underflow,
    )?;

    let epoch_duration_uint256 = Uint256::field_element_to_uint256(
        cs.namespace(|| "alloc epoch duration as uint256"),
        &epoch_duration,
    )?;
    let old_target_uint256 = Uint256::field_element_to_uint256(
        cs.namespace(|| "alloc old target as uint256"),
        old_target,
    )?;

    let (old_target_mul_epoch_duration, _) = Uint256::mul(
        cs.namespace(|| "old target * epoch duration"),
        &old_target_uint256,
        &epoch_duration_uint256,
    )?;

    let expected_epoch_duration = alloc_constant(
        cs.namespace(|| "alloc expected epoch duration"),
        Scalar::from(EXPECTED_EPOCH_TIMESPAN),
    )?;
    let expected_epoch_duration_uint256 = Uint256::field_element_to_uint256(
        cs.namespace(|| "alloc expected epoch duration as uint256"),
        &expected_epoch_duration,
    )?;

    let (new_target_uint256, _) = Uint256::unsigned_div_rem(
        cs.namespace(|| "divide (old target * epoch duration) by expected epoch duration"),
        &old_target_mul_epoch_duration,
        &expected_epoch_duration_uint256,
    )?;

    let max_target_scalar = Scalar::from_str_vartime(MAX_TARGET_DECIMAL_STR);
    let max_target = alloc_constant(
        cs.namespace(|| "alloc max target"),
        max_target_scalar.unwrap(),
    )?;
    let max_target_uint256 = Uint256::field_element_to_uint256(
        cs.namespace(|| "alloc max target as uint256"),
        &max_target,
    )?;

    let is_new_target_lte_max_target = Uint256::less_than_or_equal(
        cs.namespace(|| "is new target "),
        &new_target_uint256,
        &max_target_uint256,
    )?;

    let new_target = new_target_uint256
        .uint256_to_field_element_unchecked(cs.namespace(|| "alloc new target as field element"))?;

    let new_target = conditionally_select(
        cs.namespace(|| "clip target to max target"),
        &new_target,
        &max_target,
        &is_new_target_lte_max_target,
    )?;

    Ok(new_target)
}
