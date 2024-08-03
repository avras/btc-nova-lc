use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use ff::{PrimeField, PrimeFieldBits};

/// Allocate a variable equal to a constant
pub fn alloc_constant<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    value: Scalar,
) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let num = AllocatedNum::alloc(cs.namespace(|| "alloc num"), || Ok(value))?;

    cs.enforce(
        || "check allocated variable equals constant",
        |lc| lc + num.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + (value, CS::one()),
    );

    Ok(num)
}

/// Check that two numbers are equal and return a bit
///
/// From Nova/src/gadgets/utils.rs
pub fn alloc_num_equals<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
) -> Result<Boolean, SynthesisError> {
    // Allocate and constrain `r`: result boolean bit.
    // It equals `true` if `a` equals `b`, `false` otherwise
    let r_value = match (a.get_value(), b.get_value()) {
        (Some(a), Some(b)) => Some(a == b),
        _ => None,
    };

    let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

    // Allocate t s.t. t=1 if z1 == z2 else 1/(z1 - z2)
    let t = AllocatedNum::alloc(cs.namespace(|| "t"), || {
        match (a.get_value(), b.get_value()) {
            (Some(a_val), Some(b_val)) => {
                if a_val == b_val {
                    Ok(Scalar::ONE)
                } else {
                    Ok((a_val - b_val).invert().unwrap())
                }
            }
            (_, _) => Err(SynthesisError::AssignmentMissing),
        }
    })?;

    cs.enforce(
        || "t*(a - b) = 1 - r",
        |lc| lc + t.get_variable(),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc + CS::one() - r.get_variable(),
    );

    cs.enforce(
        || "r*(a - b) = 0",
        |lc| lc + r.get_variable(),
        |lc| lc + a.get_variable() - b.get_variable(),
        |lc| lc,
    );

    Ok(Boolean::from(r))
}

/// Check that a number is equal to a constant and return a bit
///
/// Based on alloc_num_equals which is from Nova/src/gadgets/utils.rs
pub fn alloc_num_equals_constant<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: Scalar,
) -> Result<Boolean, SynthesisError> {
    // Allocate and constrain `r`: result boolean bit.
    // It equals `true` if `a` equals `b`, `false` otherwise
    let r_value = a.get_value().map(|a_val| a_val == b);

    let r = AllocatedBit::alloc(cs.namespace(|| "r"), r_value)?;

    // Allocate t s.t. t=1 if z1 == z2 else 1/(z1 - z2)
    let t = AllocatedNum::alloc(cs.namespace(|| "t"), || match a.get_value() {
        Some(a_val) => {
            if a_val == b {
                Ok(Scalar::ONE)
            } else {
                Ok((a_val - b).invert().unwrap())
            }
        }
        _ => Err(SynthesisError::AssignmentMissing),
    })?;

    cs.enforce(
        || "t*(a - b) = 1 - r",
        |lc| lc + t.get_variable(),
        |lc| lc + a.get_variable() - (b, CS::one()),
        |lc| lc + CS::one() - r.get_variable(),
    );

    cs.enforce(
        || "r*(a - b) = 0",
        |lc| lc + r.get_variable(),
        |lc| lc + a.get_variable() - (b, CS::one()),
        |lc| lc,
    );

    Ok(Boolean::from(r))
}

/// Range check an AllocatedNum
///
/// Based on `fits_in_bits` of `bellperson-nonnative`
pub(crate) fn range_check_num<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    num_bits: usize,
) -> Result<(), SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let value_bits = a.get_value().map(|v| v.to_le_bits());

    // Allocate all but the first bit.
    let bits: Vec<Variable> = (1..num_bits)
        .map(|i| {
            cs.alloc(
                || format!("bit {i}"),
                || {
                    if let Some(bits) = &value_bits {
                        let r = if bits[i] { Scalar::ONE } else { Scalar::ZERO };
                        Ok(r)
                    } else {
                        Err(SynthesisError::AssignmentMissing)
                    }
                },
            )
        })
        .collect::<Result<_, _>>()?;

    for (i, v) in bits.iter().enumerate() {
        cs.enforce(
            || format!("bit {i} is bit"),
            |lc| lc + *v,
            |lc| lc + CS::one() - *v,
            |lc| lc,
        )
    }

    // Last bit
    cs.enforce(
        || "last bit of variable is a bit".to_string(),
        |mut lc| {
            let mut f = Scalar::ONE;
            lc = lc + a.get_variable();
            for v in bits.iter() {
                f = f.double();
                lc = lc - (f, *v);
            }
            lc
        },
        |mut lc| {
            lc = lc + CS::one();
            let mut f = Scalar::ONE;
            lc = lc - a.get_variable();
            for v in bits.iter() {
                f = f.double();
                lc = lc + (f, *v);
            }
            lc
        },
        |lc| lc,
    );

    Ok(())
}

/// Decomposes an allocated number `a` to `n_bits` allocated
/// boolean values. Returns a little-endian vector of `Boolean`
///  variables if `a` is in the range `0` to `(1 << n_bits) - 1`.
/// Otherwise, it throws an error.
pub(crate) fn num_to_bits<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    n_bits: usize,
) -> Result<Vec<Boolean>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let a_bit_values = match a.get_value() {
        Some(a_val) => {
            let mut a_bools = a_val
                .to_le_bits()
                .iter()
                .map(|b| if *b { true } else { false })
                .collect::<Vec<bool>>();
            a_bools.truncate(n_bits);
            Some(a_bools)
        }
        None => None,
    };

    let a_bits = (0..n_bits)
        .map(|i| {
            AllocatedBit::alloc(
                cs.namespace(|| format!("alloc bit {i}")),
                a_bit_values.as_ref().map(|arr| arr[i]),
            )
        })
        .collect::<Result<Vec<_>, SynthesisError>>()?
        .into_iter()
        .map(Boolean::from)
        .collect::<Vec<Boolean>>();

    let mut recompose_lc = LinearCombination::<Scalar>::zero();
    let mut coeff = Scalar::ONE;
    for b in a_bits.iter() {
        recompose_lc = recompose_lc + &b.lc(CS::one(), coeff);
        coeff = coeff.double();
    }
    cs.enforce(
        || "Check recomposed value equals original value",
        |lc| lc + &recompose_lc,
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable(),
    );

    Ok(a_bits)
}

/// Allocates a field element from a little-endian byte vector.
/// The bytes themselves are represented as a `Boolean` vector.
/// Note that the bytes themselves have the most significant
/// bit appearing first. The input vector has the least
/// significant byte appearing first.
pub(crate) fn le_bytes_to_alloc_num<Scalar, CS>(
    mut cs: CS,
    bytes_le: &Vec<Boolean>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert!(bytes_le.len() % 8 == 0);
    assert!(bytes_le.len() <= Scalar::CAPACITY as usize);

    let bytes_be = bytes_le.chunks(8).rev().collect::<Vec<_>>().concat();
    let (num_value, _) =
        bytes_be
            .iter()
            .rev()
            .fold(
                (Some(Scalar::ZERO), Scalar::ONE),
                |(acc, coeff), b| match b.get_value() {
                    Some(b_val) => {
                        if b_val {
                            (acc.map(|a| a + coeff), coeff.double())
                        } else {
                            (acc, coeff.double())
                        }
                    }
                    None => (None, coeff.double()),
                },
            );

    let num = AllocatedNum::alloc(cs.namespace(|| "alloc num"), || {
        num_value.ok_or(SynthesisError::AssignmentMissing)
    })?;

    cs.enforce(
        || "check num consistency with num bits",
        |mut lc| {
            let mut coeff = Scalar::ONE;
            for b in bytes_be.iter().rev() {
                lc = lc + &b.lc(CS::one(), coeff);
                coeff = coeff.double();
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc + num.get_variable(),
    );

    Ok(num)
}

/// Takes two allocated numbers (a, b) that are assumed
/// to be in the range `0` to `(1 << n_bits) - 1`.
/// Returns an allocated `Boolean`` variable with value `true`
/// if the `a` and `b` are such that a is strictly less than b,
/// `false` otherwise. Implementation is based on LessThan in
/// circomlib https://github.com/iden3/circomlib/blob/master/circuits/comparators.circom
pub(crate) fn less_than<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    n_bits: usize,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    assert!(n_bits < Scalar::CAPACITY as usize);
    let mut power_of_two = Scalar::ONE;
    for _ in 0..n_bits {
        power_of_two = power_of_two.double();
    }

    let offset_diff = AllocatedNum::alloc(cs.namespace(|| "alloc a + 2^n_bits - b"), || {
        match (a.get_value(), b.get_value()) {
            (Some(a_val), Some(b_val)) => Ok(a_val + power_of_two - b_val),
            (_, _) => Err(SynthesisError::AssignmentMissing),
        }
    })?;

    cs.enforce(
        || "check value of offset_diff",
        |lc| lc + offset_diff.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + a.get_variable() + (power_of_two, CS::one()) - b.get_variable(),
    );

    let offset_diff_bits = num_to_bits(
        &mut cs.namespace(|| "decompose offset_diff"),
        &offset_diff,
        n_bits + 1,
    )?;

    Ok(offset_diff_bits[n_bits].not())
}

/// Takes two allocated numbers (a, b) that are assumed
/// to be in the range `0` to `(1 << n_bits) - 1`.
/// Returns an allocated `Boolean`` variable with value `true`
/// if the `a` and `b` are such that a is less than or equal to b,
/// `false` otherwise
pub(crate) fn less_than_or_equal<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    n_bits: usize,
) -> Result<Boolean, SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let is_b_lt_a = less_than(cs.namespace(|| "b < a"), b, a, n_bits)?;
    Ok(is_b_lt_a.not())
}

// From Nova/src/gadgets/utils.rs
/// If condition return a otherwise b
pub(crate) fn conditionally_select<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
    b: &AllocatedNum<Scalar>,
    condition: &Boolean,
) -> Result<AllocatedNum<Scalar>, SynthesisError> {
    let c = AllocatedNum::alloc(cs.namespace(|| "conditional select result"), || {
        if *condition.get_value().get()? {
            Ok(*a.get_value().get()?)
        } else {
            Ok(*b.get_value().get()?)
        }
    })?;

    // a * condition + b*(1-condition) = c ->
    // a * condition - b*condition = c - b
    cs.enforce(
        || "conditional select constraint",
        |lc| lc + a.get_variable() - b.get_variable(),
        |_| condition.lc(CS::one(), Scalar::ONE),
        |lc| lc + c.get_variable() - b.get_variable(),
    );

    Ok(c)
}

/// Split a allocated field element in the range 0 to 2^192-1
/// into two parts in the range 0 to 2^64-1 and 0 to 2^128-1
pub(crate) fn split_64_128<Scalar, CS>(
    mut cs: CS,
    a: &AllocatedNum<Scalar>,
) -> Result<(AllocatedNum<Scalar>, AllocatedNum<Scalar>), SynthesisError>
where
    Scalar: PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
{
    let a_bits_192 = num_to_bits(cs.namespace(|| "decompose into 192 bits"), a, 192)?;

    let (a_bits_low, a_bits_high) = a_bits_192.split_at(64);

    let a_low = AllocatedNum::alloc(cs.namespace(|| "allow 64-bit lower part"), || {
        let mut val = Some(Scalar::ZERO);
        let mut coeff = Scalar::ONE;

        for b in a_bits_low {
            if b.get_value().is_none() {
                val = None;
                break;
            } else {
                if b.get_value().unwrap() {
                    val = val.map(|v| v + coeff)
                }
            }
            coeff = coeff.double();
        }

        match val {
            Some(v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing),
        }
    })?;

    let a_high = AllocatedNum::alloc(cs.namespace(|| "allow 64-bit higher part"), || {
        let mut val = Some(Scalar::ZERO);
        let mut coeff = Scalar::ONE;

        for b in a_bits_high {
            if b.get_value().is_none() {
                val = None;
                break;
            } else {
                if b.get_value().unwrap() {
                    val = val.map(|v| v + coeff)
                }
            }
            coeff = coeff.double();
        }

        match val {
            Some(v) => Ok(v),
            None => Err(SynthesisError::AssignmentMissing),
        }
    })?;

    // Check that lower limb is consistent with 64 lower order bits
    cs.enforce(
        || "lower limb consistency",
        |mut lc| {
            let mut f = Scalar::ONE;
            lc = lc + a_low.get_variable();

            for b in a_bits_low.iter() {
                lc = lc - &b.lc(CS::one(), f);
                f = f.double();
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc,
    );

    // Check that higher limb is consistent with 128 higher order bits
    cs.enforce(
        || "higher limb consistency",
        |mut lc| {
            let mut f = Scalar::ONE;
            lc = lc + a_high.get_variable();

            for b in a_bits_high.iter() {
                lc = lc - &b.lc(CS::one(), f);
                f = f.double();
            }
            lc
        },
        |lc| lc + CS::one(),
        |lc| lc,
    );

    Ok((a_low, a_high))
}

#[cfg(test)]
pub(crate) fn target_scalar_from_u32<Scalar: PrimeField>(t: u32) -> Scalar {
    let t_be_bytes = u32::to_be_bytes(t);
    assert!(t_be_bytes[0] >= 3u8);

    let exponent = t_be_bytes[0] - 3u8;

    let base = Scalar::from(256);
    let mantissa = Scalar::from(t_be_bytes[1] as u64) * base.square()
        + Scalar::from(t_be_bytes[2] as u64) * base
        + Scalar::from(t_be_bytes[3] as u64);

    let mut s = mantissa;
    for _i in 0..exponent {
        s = s * base;
    }
    s
}
