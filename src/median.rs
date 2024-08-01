use bellpepper_core::{
    boolean::Boolean, num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::PrimeFieldBits;

use crate::utils::{alloc_num_equals, less_than, less_than_or_equal};

pub(crate) const NUM_TIMESTAMP_BITS: usize = 32;

pub(crate) fn alloc_median_timestamp<Scalar, CS>(
    mut cs: CS,
    timestamps: &Vec<AllocatedNum<Scalar>>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert_eq!(timestamps.len(), 11);

    let timestamps_u64 = timestamps
        .iter()
        .map(|ts| {
            ts.get_value().map(|ts_scalar| {
                let mut ts_u64 = 0u64;
                let mut coeff = 1u64;
                let ts_bits = ts_scalar.to_le_bits();
                // Timestamps are guaranteed to fit in 32 bit
                for i in 0..NUM_TIMESTAMP_BITS {
                    if ts_bits[i] {
                        ts_u64 += coeff;
                    }
                    coeff = 2 * coeff;
                }
                ts_u64
            })
        })
        .collect::<Option<Vec<_>>>();

    AllocatedNum::alloc(cs.namespace(|| "alloc median"), || match timestamps_u64 {
        Some(mut t_values) => {
            t_values.sort();
            let median_value = t_values[5];
            Ok(Scalar::from(median_value as u64))
        }
        None => Err(SynthesisError::AssignmentMissing),
    })
}

pub(crate) fn compute_median_timestamp<Scalar, CS>(
    mut cs: CS,
    timestamps: &Vec<AllocatedNum<Scalar>>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let median = alloc_median_timestamp(cs.namespace(|| "alloc median"), timestamps)?;
    let median_value = median.get_value();
    let timestamp_values = timestamps
        .iter()
        .map(|t| t.get_value())
        .collect::<Option<Vec<Scalar>>>();

    let n_median_occurences = AllocatedNum::alloc(
        cs.namespace(|| "Allocate number of median occurrences"),
        || match (timestamp_values, median_value) {
            (Some(tvs), Some(mv)) => {
                Ok(Scalar::from(tvs.iter().filter(|t| **t == mv).count() as u64))
            }
            (_, _) => Err(SynthesisError::AssignmentMissing),
        },
    )?;

    let mut signs_diff = LinearCombination::<Scalar>::zero();
    let mut signs_diff_value = None;
    let mut sum_equality_bits = LinearCombination::<Scalar>::zero();

    for i in 0..timestamps.len() {
        let res_eq = alloc_num_equals(
            cs.namespace(|| format!("check if median equals timestamp {i}")),
            &timestamps[i],
            &median,
        )?;

        sum_equality_bits = sum_equality_bits + &res_eq.lc(CS::one(), Scalar::ONE);

        let med_lt_ts = less_than(
            cs.namespace(|| format!("compare timestamp {i} > median")),
            &median,
            &timestamps[i],
            32,
        )?;

        let delta_sign = AllocatedNum::alloc(
            cs.namespace(|| format!("allocate delta_sign {i}")),
            || match (res_eq.get_value(), med_lt_ts.get_value()) {
                (Some(res_eq_value), Some(med_lt_ts_value)) => {
                    if res_eq_value {
                        Ok(Scalar::ZERO)
                    } else {
                        if med_lt_ts_value {
                            Ok(Scalar::ONE)
                        } else {
                            Ok(-Scalar::ONE)
                        }
                    }
                }
                (_, _) => Err(SynthesisError::AssignmentMissing),
            },
        )?;

        let two = Scalar::ONE + Scalar::ONE;

        // delta_sign = (1-res_eq)*(2*med_lt_ts - 1)
        cs.enforce(
            || format!("check delta_sign {i} value is correct"),
            |lc| lc + CS::one() + &res_eq.lc(CS::one(), -Scalar::ONE),
            |lc| lc + &med_lt_ts.lc(CS::one(), two) - CS::one(),
            |lc| lc + delta_sign.get_variable(),
        );
        signs_diff = signs_diff + delta_sign.get_variable();

        signs_diff_value = match (signs_diff_value, delta_sign.get_value()) {
            (None, None) => None,
            (None, Some(d)) => Some(d),
            (Some(s), None) => Some(s),
            (Some(s), Some(d)) => Some(s + d),
        }
    }

    cs.enforce(
        || "check number of median occurrences",
        |lc| lc + &sum_equality_bits,
        |lc| lc + CS::one(),
        |lc| lc + n_median_occurences.get_variable(),
    );

    let signs_diff_alloc = AllocatedNum::alloc(cs.namespace(|| "alloc signs_diff"), || {
        if signs_diff_value.is_some() {
            Ok(signs_diff_value.unwrap())
        } else {
            Err(SynthesisError::AssignmentMissing)
        }
    })?;
    let neg_signs_diff_alloc = AllocatedNum::alloc(
        cs.namespace(|| "alloc negative signs_diff"),
        || match signs_diff_alloc.get_value() {
            Some(v) => Ok(-v),
            None => Err(SynthesisError::AssignmentMissing),
        },
    )?;

    cs.enforce(
        || "check allocated signs_diff value",
        |lc| lc + &signs_diff,
        |lc| lc + CS::one(),
        |lc| lc + signs_diff_alloc.get_variable(),
    );

    cs.enforce(
        || "check allocated negative signs_diff value",
        |lc| lc + neg_signs_diff_alloc.get_variable(),
        |lc| lc - CS::one(),
        |lc| lc + signs_diff_alloc.get_variable(),
    );

    // Allocate 11 as an AllocateNum for use in addition and comparison
    let eleven = AllocatedNum::alloc(cs.namespace(|| "alloc 11"), || Ok(Scalar::from(11u64)))?;

    cs.enforce(
        || "check value of 11",
        |lc| lc + eleven.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + (Scalar::from(11u64), CS::one()),
    );

    let signs_diff_plus_11 =
        signs_diff_alloc.add(cs.namespace(|| "add 11 to signs_diff"), &eleven)?;

    let is_signs_diff_negative = less_than(
        cs.namespace(|| "is signs_diff negative"),
        &signs_diff_plus_11,
        &eleven,
        5,
    )?; // max(signs_diff_plus_11) = 22, fits in 5 bits

    let (abs_signs_diff, _) = AllocatedNum::conditionally_reverse(
        cs.namespace(|| "absolute value of signs_diff"),
        &signs_diff_alloc,
        &neg_signs_diff_alloc,
        &is_signs_diff_negative,
    )?;

    let abs_signs_diff_plus_1 = AllocatedNum::alloc(
        cs.namespace(|| "alloc abs_signs_diff plus 1"),
        || match abs_signs_diff.get_value() {
            Some(v) => Ok(v + Scalar::ONE),
            None => Err(SynthesisError::AssignmentMissing),
        },
    )?;

    cs.enforce(
        || "check value of abs_signs_diff_plus_1",
        |lc| lc + abs_signs_diff_plus_1.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + abs_signs_diff.get_variable() + CS::one(),
    );

    // Is abs_signs_diff_plus_1 less than or equal to n_median_occurrences?
    let is_abs_leq_nm = less_than_or_equal(
        cs.namespace(|| "check abs_signs_diff_plus_1 <= n_median_occurrences"),
        &abs_signs_diff_plus_1,
        &n_median_occurences,
        4,
    )?; // Maximum value of arguments is 12, so 4 bits are enough

    Boolean::enforce_equal(
        cs.namespace(|| "check inequality holds"),
        &is_abs_leq_nm,
        &Boolean::Constant(true),
    )?;

    Ok(median)
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use pasta_curves::Fp;

    fn test_compute_median_timestamp_helper(timestamps: &mut Vec<u32>) {
        let mut cs = TestConstraintSystem::<Fp>::new();
        assert_eq!(timestamps.len(), 11);
        timestamps.sort();
        let median = timestamps[5];

        let timestamps_alloc = timestamps
            .iter()
            .enumerate()
            .map(|(i, v)| {
                AllocatedNum::alloc(cs.namespace(|| format!("alloc timestamp {i}")), || {
                    Ok(Fp::from(*v as u64))
                })
                .unwrap()
            })
            .collect::<Vec<_>>();

        let median_alloc =
            compute_median_timestamp(cs.namespace(|| "alloc median"), &timestamps_alloc).unwrap();

        assert_eq!(Fp::from(median as u64), median_alloc.get_value().unwrap());
        assert!(cs.is_satisfied());
    }

    #[test]
    fn test_compute_median_timestamp() {
        test_compute_median_timestamp_helper(&mut vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
        test_compute_median_timestamp_helper(&mut vec![11, 2, 3, 4, 6, 6, 8, 6, 10, 9, 1]);
        test_compute_median_timestamp_helper(&mut vec![11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11]);
    }
}
