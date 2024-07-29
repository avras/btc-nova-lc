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

/// Converts a length 32 Boolean vector representing the nBits field
/// as little-endian bytes into a pair of allocated field elements.
/// The first field element is the target threshold and the second
/// element is the mask which will be used to check for equality
/// with the calculated target.
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

    let unshifted_mask = alloc_constant(
        cs.namespace(|| "alloc unshifted mask"),
        Scalar::from(MANTISSA_MASK),
    )?;
    let mask = unshifted_mask.mul(cs.namespace(|| "unshifted mask * multiplier"), &multiplier)?;

    Ok((expected_target, mask))
}

/// Calculates the new target from the old target, the epoch start time,
/// and the epoch end time. This calculation happens at blocks whose
/// height is divisible by 2016. The epoch start time is the timestamp
/// in the previous block whose height is divisible by 2016. The epoch
/// end time is the timestamp of the predecessor block.
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

/// Verifies that the nBits fields in the current block header is
/// consistent with the recalculated target. Returns the target which
/// is calculated from the nBits field.
pub(crate) fn verify_target<Scalar, CS>(
    mut cs: CS,
    nbits: &Vec<Boolean>,
    old_target: &AllocatedNum<Scalar>,
    epoch_start_time: &AllocatedNum<Scalar>,
    epoch_end_time: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let (expected_target, mask) =
        nbits_to_target(cs.namespace(|| "convert nbits to target and mask"), nbits)?;
    let calculated_target = calc_new_target(
        cs.namespace(|| "calculate target"),
        old_target,
        epoch_start_time,
        epoch_end_time,
    )?;

    let expected_target_bits =
        expected_target.to_bits_le(cs.namespace(|| "get expected target bits"))?;
    let mask_bits = mask.to_bits_le(cs.namespace(|| "get mask bits"))?;
    let calculated_target_bits =
        calculated_target.to_bits_le(cs.namespace(|| "get calculated target bits"))?;

    for i in 0..mask_bits.len() {
        let masked_calculated_target_bit = Boolean::and(
            cs.namespace(|| format!("mask {i} AND calc target bit {i}")),
            &mask_bits[i],
            &calculated_target_bits[i],
        )?;
        Boolean::enforce_equal(
            cs.namespace(|| format!("check target bits equality {i}")),
            &masked_calculated_target_bit,
            &expected_target_bits[i],
        )?;
    }

    Ok(expected_target)
}
// Logic from https://github.com/bitcoin/bitcoin/blob/v0.16.2/src/chain.cpp#L121
/// Compute accumulated chainwork as old_chainwork + ~target(target + 1) + 1
pub(crate) fn accumulate_chainwork<Scalar, CS>(
    mut cs: CS,
    old_chainwork: &AllocatedNum<Scalar>,
    target: &AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let target_uint256 =
        Uint256::field_element_to_uint256(cs.namespace(|| "alloc target as uint256"), target)?;

    let one_uint256 = Uint256::one(cs.namespace(|| "alloc one"))?;

    let not_target_uint256 = target_uint256.not(cs.namespace(|| "bitwise not of target"))?;
    let (target_uint256_plus_one, _) = Uint256::add(
        cs.namespace(|| "add one to target"),
        &target_uint256,
        &one_uint256,
    )?;

    let (ratio_uint256, _) = Uint256::unsigned_div_rem(
        cs.namespace(|| "~(target) div (target+1)"),
        &not_target_uint256,
        &target_uint256_plus_one,
    )?;
    let (ratio_plus_one_uint256, _) = Uint256::add(
        cs.namespace(|| "add one to ratio"),
        &ratio_uint256,
        &one_uint256,
    )?;

    let block_work = ratio_plus_one_uint256
        .uint256_to_field_element_unchecked(cs.namespace(|| "get block work field element"))?;
    let chainwork = old_chainwork.add(
        cs.namespace(|| "add block work to old chain work"),
        &block_work,
    )?;

    Ok(chainwork)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::PrimeField;
    use pasta_curves::Fp;

    fn target_scalar_from_u32(t: u32) -> Fp {
        let t_be_bytes = u32::to_be_bytes(t);
        assert!(t_be_bytes[0] >= 3u8);

        let exponent = t_be_bytes[0] - 3u8;

        let base = Fp::from(256);
        let mantissa = Fp::from(t_be_bytes[1] as u64) * base.square()
            + Fp::from(t_be_bytes[2] as u64) * base
            + Fp::from(t_be_bytes[3] as u64);

        let mut s = mantissa;
        for _i in 0..exponent {
            s = s * base;
        }
        s
    }

    #[test]
    fn test_nbits_to_target() {
        let mut cs = TestConstraintSystem::<Fp>::new();

        // nbits values from blocks 0, 100k, 200k, ..., 800k
        let max_nbits_vec: Vec<u32> = vec![
            0x1D00FFFF, 0x1B04864C, 0x1A05DB8B, 0x1900896C, 0x1806B99F, 0x18009645, 0x1715A35C,
            0x170F48E4, 0x17053894,
        ];

        let _ = max_nbits_vec.into_iter().enumerate().map(|(j, nbits_u32)| {
            let max_nbits_le_bytes = u32::to_le_bytes(nbits_u32);
            let max_nbits_bits_le = max_nbits_le_bytes
                .iter()
                .flat_map(|b| {
                    (0..8)
                        .rev()
                        .map(|i| b & (1 << i) == (1 << i))
                        .collect::<Vec<bool>>()
                })
                .collect::<Vec<bool>>();

            let max_nbits_boolean_vec = max_nbits_bits_le
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    Boolean::from(
                        AllocatedBit::alloc(cs.namespace(|| format!("bit {j} {i}")), Some(*b))
                            .unwrap(),
                    )
                })
                .collect::<Vec<_>>();

            let res = nbits_to_target(
                cs.namespace(|| format!("alloc target {j}")),
                &max_nbits_boolean_vec,
            );
            assert!(res.is_ok());

            let (target, _) = res.unwrap();
            let expected_target_value = target_scalar_from_u32(nbits_u32);
            assert_eq!(target.get_value().unwrap(), expected_target_value);
        });

        assert!(cs.is_satisfied())
    }

    #[test]
    fn test_calc_new_target() {
        let mut cs = TestConstraintSystem::<Fp>::new();

        let test_cases = vec![
            (
                // block 2016
                "26959535291011309493156476344723991336010898738574164086137773096960",
                "1231006505",
                "1233061996",
                "26959535291011309493156476344723991336010898738574164086137773096960",
            ),
            (
                // block 90720
                "8719867261221084516486306056196045840260667577454435863762042880",
                "1288479527",
                "1289303926",
                "5942997561411541711563156602531385577600077786198627208704997014",
            ),
            (
                // block 92736
                "5942996718418989293499865695368015163438891473576991811912597504",
                "1289305768",
                "1290104845",
                "3926018509229572344313816286588613965571477415700629866143917555",
            ),
            (
                // block 94752
                "3926013280397599483741094494745234959951218212740030386090803200",
                "1290105874",
                "1291134100",
                "3337325505332425700040650320729095537310516946108490809993884103",
            ),
            (
                // block 96768
                "3337321571246095014985518819479127172783474909736415373333364736",
                "1291135075",
                "1291932610",
                "2200422254731939804709388022233205762025354383380152145148334197",
            ),
            (
                // block 98784
                "2200419182034594781720344474937177839165432393990533906392154112",
                "1291933202",
                "1292956393",
                "1861317049673577272902795125376526066826651733332976503154178702",
            ),
        ];

        for i in 0..test_cases.len() {
            let (old_target, epoch_start_ts, epoch_end_ts, new_target) = test_cases[i];

            let old_target = alloc_constant(
                cs.namespace(|| format!("alloc old target {i}")),
                Fp::from_str_vartime(&old_target).unwrap(),
            )
            .unwrap();
            let new_target = alloc_constant(
                cs.namespace(|| format!("alloc new target {i}")),
                Fp::from_str_vartime(&new_target).unwrap(),
            )
            .unwrap();
            let epoch_start_ts = alloc_constant(
                cs.namespace(|| format!("alloc epoch start {i}")),
                Fp::from_str_vartime(&epoch_start_ts).unwrap(),
            )
            .unwrap();
            let epoch_end_ts = alloc_constant(
                cs.namespace(|| format!("alloc epoch end {i}")),
                Fp::from_str_vartime(&epoch_end_ts).unwrap(),
            )
            .unwrap();

            let res = calc_new_target(
                cs.namespace(|| format!("calculate new target {i}")),
                &old_target,
                &epoch_start_ts,
                &epoch_end_ts,
            );
            assert!(res.is_ok());

            let calc_new_target = res.unwrap();
            assert_eq!(
                calc_new_target.get_value().unwrap(),
                new_target.get_value().unwrap()
            );
        }

        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_accumulate_chainwork() {
        let mut cs = TestConstraintSystem::<Fp>::new();
        let test_cases = vec![
            (0x0u128, 0x1d00ffffu32, 0x100010001u128), // block 0
            (0x7dff7dff7dffu128, 0x1d00ffffu32, 0x7e007e007e00u128), // block 32255
            (0x7e007e007e00u128, 0x1d00d86au32, 0x7e01acd42dd2u128), // block 32256
            (0x6445a568dea41a2u128, 0x1b04864cu32, 0x64492eaf00f2520u128), // block 99999
        ];
        for i in 0..test_cases.len() {
            let (old_chainwork, target, new_chainwork) = test_cases[i];

            let res = alloc_constant(
                cs.namespace(|| format!("alloc old chainwork {i}")),
                Fp::from_u128(old_chainwork),
            );
            assert!(res.is_ok());
            let old_chainwork = res.unwrap();

            let res = alloc_constant(
                cs.namespace(|| format!("alloc target {i}")),
                target_scalar_from_u32(target),
            );
            assert!(res.is_ok());
            let target = res.unwrap();

            let res = alloc_constant(
                cs.namespace(|| format!("alloc new chainwork {i}")),
                Fp::from_u128(new_chainwork),
            );
            assert!(res.is_ok());
            let new_chainwork = res.unwrap();

            let res = accumulate_chainwork(
                cs.namespace(|| format!("accumulate chainwork {i}")),
                &old_chainwork,
                &target,
            );
            assert!(res.is_ok());
            let calculated_new_chainwork = res.unwrap();

            assert_eq!(
                new_chainwork.get_value().unwrap(),
                calculated_new_chainwork.get_value().unwrap()
            );
        }
        assert!(cs.is_satisfied());
    }
}
