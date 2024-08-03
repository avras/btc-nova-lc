use bellpepper::gadgets::Assignment;
use bellpepper_core::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    ConstraintSystem, SynthesisError,
};
use ff::PrimeFieldBits;
use num_bigint::BigUint;

use crate::utils::{alloc_constant, alloc_num_equals, less_than, range_check_num, split_64_128};

/// Represents an 256-bit unsigned integer
pub(crate) struct Uint256<Scalar: PrimeFieldBits> {
    low: AllocatedNum<Scalar>,  // Lower 128 bits
    high: AllocatedNum<Scalar>, // Higher 128 bits
    value: Option<BigUint>,
}

impl<Scalar> Uint256<Scalar>
where
    Scalar: PrimeFieldBits,
{
    pub(crate) fn one<CS>(mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let one_fe = alloc_constant(cs.namespace(|| "alloc one"), Scalar::ONE)?;
        let zero_fe = alloc_constant(cs.namespace(|| "alloc zero"), Scalar::ZERO)?;

        Ok(Self {
            low: one_fe,
            high: zero_fe,
            value: Some(BigUint::from(1u8)),
        })
    }

    /// Check that the representation of the integer is correct
    pub(crate) fn check_limbs<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        range_check_num(&mut cs.namespace(|| "check lower limb"), &self.low, 128)?;
        range_check_num(&mut cs.namespace(|| "check higher limb"), &self.high, 128)?;
        Ok(())
    }

    /// Obtain a [Uint256] from a field element
    ///
    /// The number of bits required to represent the field element
    /// must be at most 256
    pub(crate) fn field_element_to_uint256<CS>(
        mut cs: CS,
        a: &AllocatedNum<Scalar>,
    ) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        assert!(Scalar::NUM_BITS <= 256);

        let a_bits = a.to_bits_le_strict(cs.namespace(|| "get strict LE bits"))?;

        let mut val_bigint = Some(BigUint::ZERO);
        let mut coeff_bigint = BigUint::new(vec![1, 0, 0, 0, 0, 0, 0, 0]);

        for b in &a_bits {
            if b.get_value().is_none() {
                val_bigint = None;
                break;
            } else {
                if b.get_value().unwrap() {
                    val_bigint = val_bigint.map(|v| v + coeff_bigint.clone());
                }
            }
            coeff_bigint = coeff_bigint.clone() + coeff_bigint;
        }

        let (low_bits, high_bits) = a_bits.split_at(128);

        let mut low_value: Option<Scalar> = Some(Scalar::ZERO);
        let mut f = Scalar::ONE;

        for b in low_bits {
            if b.get_value().is_none() {
                low_value = None;
                break;
            } else {
                if b.get_value().unwrap() {
                    low_value = low_value.map(|v| v + f);
                }
            }
            f = f.double();
        }

        let mut high_value: Option<Scalar> = Some(Scalar::ZERO);
        f = Scalar::ONE;

        for b in high_bits {
            if b.get_value().is_none() {
                high_value = None;
                break;
            } else {
                if b.get_value().unwrap() {
                    high_value = high_value.map(|v| v + f);
                }
            }
            f = f.double();
        }

        let low_limb = AllocatedNum::alloc(cs.namespace(|| "alloc lower limb"), || {
            low_value.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let high_limb = AllocatedNum::alloc(cs.namespace(|| "alloc higher limb"), || {
            high_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Check that lower limb is consistent with lower order bits
        cs.enforce(
            || "lower limb consistency",
            |mut lc| {
                let mut f = Scalar::ONE;
                lc = lc + low_limb.get_variable();

                for b in low_bits.iter() {
                    lc = lc - &b.lc(CS::one(), f);
                    f = f.double();
                }
                lc
            },
            |lc| lc + CS::one(),
            |lc| lc,
        );

        // Check that higher limb is consistent with higher order bits
        cs.enforce(
            || "higher limb consistency",
            |mut lc| {
                let mut f = Scalar::ONE;
                lc = lc + high_limb.get_variable();

                for b in high_bits.iter() {
                    lc = lc - &b.lc(CS::one(), f);
                    f = f.double();
                }
                lc
            },
            |lc| lc + CS::one(),
            |lc| lc,
        );

        Ok(Uint256 {
            low: low_limb,
            high: high_limb,
            value: val_bigint,
        })
    }

    /// Converts a uint256 to a field element without checking
    /// for overflows.
    pub(crate) fn uint256_to_field_element_unchecked<CS>(
        &self,
        mut cs: CS,
    ) -> Result<AllocatedNum<Scalar>, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let pow128 = Scalar::from_u128(u128::MAX) + Scalar::ONE;

        let fe = AllocatedNum::alloc(cs.namespace(|| "alloc field element"), || {
            match (self.low.get_value(), self.high.get_value()) {
                (Some(lv), Some(hv)) => Ok(lv + hv * pow128),
                (_, _) => Err(SynthesisError::AssignmentMissing),
            }
        })?;

        cs.enforce(
            || "check field element value",
            |lc| lc + self.low.get_variable() + (pow128, self.high.get_variable()),
            |lc| lc + CS::one(),
            |lc| lc + fe.get_variable(),
        );

        Ok(fe)
    }

    /// Returns a true Boolean if `a` < `b``. The limbs of `a` and `b` are
    /// assumed to be in the range 0 to 2^128 - 1.
    pub(crate) fn less_than<CS>(mut cs: CS, a: &Self, b: &Self) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let high_limbs_equal = alloc_num_equals(
            &mut cs.namespace(|| "check equality of high limbs"),
            &a.high,
            &b.high,
        )?;

        let a_low_lt_b_low = less_than(&mut cs.namespace(|| "a.low < b.low"), &a.low, &b.low, 128)?;
        let a_high_lt_b_high = less_than(
            &mut cs.namespace(|| "a.high < b.high"),
            &a.high,
            &b.high,
            128,
        )?;

        let tmp = Boolean::and(
            cs.namespace(|| "(a.high == b.high) AND (a.low < b.low)"),
            &high_limbs_equal,
            &a_low_lt_b_low,
        )?;

        Boolean::or(
            cs.namespace(|| "(a.high < b.high) OR [(a.high == b.high) AND (a.low < b.low)] "),
            &a_high_lt_b_high,
            &tmp,
        )
    }

    /// Returns a true Boolean if `a` <= `b``. The limbs of `a` and `b` are
    /// assumed to be in the range 0 to 2^128 - 1.
    pub(crate) fn less_than_or_equal<CS>(
        mut cs: CS,
        a: &Self,
        b: &Self,
    ) -> Result<Boolean, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let is_b_lt_a = Self::less_than(cs.namespace(|| "b < a"), b, a)?;
        Ok(is_b_lt_a.not())
    }

    /// Enforces `a` == `b`.
    pub(crate) fn enforce_equal<CS>(mut cs: CS, a: &Self, b: &Self) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        cs.enforce(
            || "check low limbs are equal",
            |lc| lc + a.low.get_variable() - b.low.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );
        cs.enforce(
            || "check high limbs are equal",
            |lc| lc + a.high.get_variable() - b.high.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        Ok(())
    }

    /// Enforces `a` == `0`.
    pub(crate) fn enforce_equal_zero<CS>(&self, mut cs: CS) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        cs.enforce(
            || "check low limb is zero",
            |lc| lc + self.low.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );
        cs.enforce(
            || "check high limb is zero",
            |lc| lc + self.high.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc,
        );

        Ok(())
    }

    /// Complements the bits of a uint256. If the limbs of the input uint256 are
    /// in 128-bit field elements, then the limbs of the complemented uint256 are
    /// also 128-bit field elements
    pub(crate) fn not<CS>(&self, mut cs: CS) -> Result<Self, SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        assert!(Scalar::CAPACITY >= 128);
        let ones_128 = Scalar::from_u128(u128::MAX);

        let low_not = AllocatedNum::alloc(cs.namespace(|| "alloc complemented low limb"), || {
            self.low
                .get_value()
                .map(|val| ones_128 - val)
                .ok_or(SynthesisError::AssignmentMissing)
        })?;
        let high_not =
            AllocatedNum::alloc(cs.namespace(|| "alloc complemented high limb"), || {
                self.high
                    .get_value()
                    .map(|val| ones_128 - val)
                    .ok_or(SynthesisError::AssignmentMissing)
            })?;

        cs.enforce(
            || "check complemented low limb value",
            |lc| lc + self.low.get_variable() + low_not.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + (ones_128, CS::one()),
        );
        cs.enforce(
            || "check complemented high limb value",
            |lc| lc + self.high.get_variable() + high_not.get_variable(),
            |lc| lc + CS::one(),
            |lc| lc + (ones_128, CS::one()),
        );

        let all_ones_bigint = BigUint::from_bytes_le(&[0xFF; 32]);
        let complemented_bigint = self.value.as_ref().map(|x| all_ones_bigint - x);

        Ok(Uint256 {
            low: low_not,
            high: high_not,
            value: complemented_bigint,
        })
    }

    /// Returns the modulo 2^256 sum of two uint256 variables and a carry bit
    pub(crate) fn add<CS>(mut cs: CS, a: &Self, b: &Self) -> Result<(Self, Boolean), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let ones_128_bigint = BigUint::from_bytes_le(&[0xFF; 16]);

        let a_low_bigint = a.value.as_ref().map(|x| x & &ones_128_bigint);
        let a_high_bigint = a.value.as_ref().map(|x| x >> 128);
        let b_low_bigint = b.value.as_ref().map(|x| x & &ones_128_bigint);
        let b_high_bigint = b.value.as_ref().map(|x| x >> 128);

        let sum_low = a_low_bigint.and_then(|a_l| b_low_bigint.and_then(|b_l| Some(a_l + b_l)));
        let carry_low = sum_low.map(|s| s > ones_128_bigint);

        let sum_high = match (a_high_bigint, b_high_bigint, carry_low) {
            (Some(a_h), Some(b_h), Some(c_l)) => Some(a_h + b_h + BigUint::from(c_l)),
            (_, _, _) => None,
        };
        let carry_high = sum_high.map(|s| s > ones_128_bigint);

        let carry_low_alloc = Boolean::from(AllocatedBit::alloc(
            cs.namespace(|| "alloc carry_low bit"),
            carry_low,
        )?);
        let carry_high_alloc = Boolean::from(AllocatedBit::alloc(
            cs.namespace(|| "alloc carry_high bit"),
            carry_high,
        )?);

        let pow128 = Scalar::from_u128(u128::MAX) + Scalar::ONE;

        let res_low = AllocatedNum::alloc(cs.namespace(|| "allow sum low"), || {
            match (a.low.get_value(), b.low.get_value(), carry_low) {
                (Some(a_l), Some(b_l), Some(c_l)) => {
                    if c_l {
                        Ok(a_l + b_l - pow128)
                    } else {
                        Ok(a_l + b_l)
                    }
                }
                (_, _, _) => Err(SynthesisError::AssignmentMissing),
            }
        })?;
        let res_high = AllocatedNum::alloc(cs.namespace(|| "allow sum high"), || {
            match (
                a.high.get_value(),
                b.high.get_value(),
                carry_low,
                carry_high,
            ) {
                (Some(a_h), Some(b_h), Some(c_l), Some(c_h)) => {
                    let mut sum_h = a_h + b_h;
                    if c_l {
                        sum_h += Scalar::ONE;
                    }
                    if c_h {
                        sum_h -= pow128;
                    }
                    Ok(sum_h)
                }
                (_, _, _, _) => Err(SynthesisError::AssignmentMissing),
            }
        })?;

        cs.enforce(
            || "check res_low == a.low + b.low - carry_low * (2^128) ",
            |lc| {
                lc + a.low.get_variable()
                    + b.low.get_variable()
                    + &carry_low_alloc.lc(CS::one(), -pow128)
            },
            |lc| lc + CS::one(),
            |lc| lc + res_low.get_variable(),
        );

        cs.enforce(
            || "check res_high == a.high + b.high + carry_low - carry_high * (2^128) ",
            |lc| {
                lc + a.high.get_variable()
                    + b.high.get_variable()
                    + &carry_low_alloc.lc(CS::one(), Scalar::ONE)
                    + &carry_high_alloc.lc(CS::one(), -pow128)
            },
            |lc| lc + CS::one(),
            |lc| lc + res_high.get_variable(),
        );

        let pow256_bigint = BigUint::from(1u8) << 256;
        let res_value = a.value.as_ref().and_then(|a_val| {
            b.value
                .as_ref()
                .and_then(|b_val| Some((a_val + b_val) % pow256_bigint))
        });

        let res = Uint256 {
            low: res_low,
            high: res_high,
            value: res_value,
        };

        // Range check limbs
        res.check_limbs(&mut cs.namespace(|| "range check limbs of sum"))?;

        Ok((res, carry_high_alloc))
    }

    /// Returns the product of two uint256 variables as a pair of uint256 variables
    pub(crate) fn mul<CS>(mut cs: CS, a: &Self, b: &Self) -> Result<(Self, Self), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let (a0, a1) = split_64_128(cs.namespace(|| "split a.low"), &a.low)?;
        let (a2, a3) = split_64_128(cs.namespace(|| "split a.high"), &a.high)?;
        let (b0, b1) = split_64_128(cs.namespace(|| "split b.low"), &b.low)?;
        let (b2, b3) = split_64_128(cs.namespace(|| "split b.high"), &b.high)?;

        // Least significant limb: a0*b0
        let a0b0 = a0.mul(cs.namespace(|| "a0*b0"), &b0)?;
        let (res0, carry) = split_64_128(&mut cs.namespace(|| "split a0*b0"), &a0b0)?;

        // Limb with coefficient 2^64: a0*b1 + a1*b0 + carry
        let a0b1 = a0.mul(cs.namespace(|| "a0*b1"), &b1)?;
        let a1b0 = a1.mul(cs.namespace(|| "a1*b0"), &b0)?;
        let a0b1_a1b0_carry = a0b1
            .add(cs.namespace(|| "a0*b1 + a1*b0"), &a1b0)?
            .add(cs.namespace(|| "a0*b1 + a1*b0 + carry"), &carry)?;
        let (res1, carry) = split_64_128(
            &mut cs.namespace(|| "split a0*b1 + a1*b0 + carry"),
            &a0b1_a1b0_carry,
        )?;

        // Limb with coefficient 2^128: a0*b2 + a1*b1 + a2*b0 + carry
        let a0b2 = a0.mul(cs.namespace(|| "a0*b2"), &b2)?;
        let a1b1 = a1.mul(cs.namespace(|| "a1*b1"), &b1)?;
        let a2b0 = a2.mul(cs.namespace(|| "a2*b0"), &b0)?;
        let a0b2_a1b1_a2b0_carry = a0b2
            .add(cs.namespace(|| "a0*b2 + a1*b1"), &a1b1)?
            .add(cs.namespace(|| "a0*b2 + a1*b1 + a2*b0"), &a2b0)?
            .add(cs.namespace(|| "a0*b2 + a1*b1 + a2*b0 + carry"), &carry)?;
        let (res2, carry) = split_64_128(
            &mut cs.namespace(|| "split a0*b2 + a1*b1 + a2*b0 + carry"),
            &a0b2_a1b1_a2b0_carry,
        )?;

        // Limb with coefficient 2^192: a0*b3 + a1*b2 + a2*b1 + a3*b0 + carry
        let a0b3 = a0.mul(cs.namespace(|| "a0*b3"), &b3)?;
        let a1b2 = a1.mul(cs.namespace(|| "a1*b2"), &b2)?;
        let a2b1 = a2.mul(cs.namespace(|| "a2*b1"), &b1)?;
        let a3b0 = a3.mul(cs.namespace(|| "a3*b0"), &b0)?;
        let a0b3_a1b2_a2b1_a3b0_carry = a0b3
            .add(cs.namespace(|| "a0*b3 + a1*b2"), &a1b2)?
            .add(cs.namespace(|| "a0*b3 + a1*b2 + a2*b1"), &a2b1)?
            .add(cs.namespace(|| "a0*b3 + a1*b2 + a2*b1 + a3*b0"), &a3b0)?
            .add(
                cs.namespace(|| "a0*b3 + a1*b2 + a2*b1 + a3*b0 + carry"),
                &carry,
            )?;
        let (res3, carry) = split_64_128(
            &mut cs.namespace(|| "split a0*b3 + a1*b2 + a2*b1 + a3*b0 + carry"),
            &a0b3_a1b2_a2b1_a3b0_carry,
        )?;

        // Limb with coefficient 2^256: a1*b3 + a2*b2 + a3*b1 + carry
        let a1b3 = a1.mul(cs.namespace(|| "a1*b3"), &b3)?;
        let a2b2 = a2.mul(cs.namespace(|| "a2*b2"), &b2)?;
        let a3b1 = a3.mul(cs.namespace(|| "a3*b1"), &b1)?;
        let a1b3_a2b2_a3b1_carry = a1b3
            .add(cs.namespace(|| "a1*b3 + a2*b2"), &a2b2)?
            .add(cs.namespace(|| "a1*b3 + a2*b2 + a3*b1"), &a3b1)?
            .add(cs.namespace(|| "a1*b3 + a2*b2 + a3*b1 + carry"), &carry)?;
        let (res4, carry) = split_64_128(
            &mut cs.namespace(|| "split a1*b3 + a2*b2 + a3*b1 + carry"),
            &a1b3_a2b2_a3b1_carry,
        )?;

        // Limb with coefficient 2^320: a2*b3 + a3*b2 + carry
        let a2b3 = a2.mul(cs.namespace(|| "a2*b3"), &b3)?;
        let a3b2 = a3.mul(cs.namespace(|| "a3*b2"), &b2)?;
        let a2b3_a3b2_carry = a2b3
            .add(cs.namespace(|| "a2*b3 + a3*b2"), &a3b2)?
            .add(cs.namespace(|| "a2*b3 + a3*b2 + carry"), &carry)?;
        let (res5, carry) = split_64_128(
            &mut cs.namespace(|| "split a2*b3 + a3*b2 + carry"),
            &a2b3_a3b2_carry,
        )?;

        // Limb with coefficient 2^384: a3*b3 + carry
        let a3b3_carry = a3
            .mul(cs.namespace(|| "a3*b3"), &b3)?
            .add(cs.namespace(|| "a3*b3 + carry"), &carry)?;
        let (res6, carry) = split_64_128(&mut cs.namespace(|| "split a3*b3 + carry"), &a3b3_carry)?;

        let pow64 = Scalar::from_u128(1u128 << 64);

        // Lower limb of the less significant uint256
        let low0 =
            AllocatedNum::alloc(cs.namespace(|| "alloc lower limb of lower uint256"), || {
                Ok(*res0.get_value().get()? + pow64 * *res1.get_value().get()?)
            })?;
        // Check that low0 is consistent with res0 and res1
        cs.enforce(
            || "check low0 == res0 +  (2^64) * res1",
            |lc| lc + res0.get_variable() + (pow64, res1.get_variable()),
            |lc| lc + CS::one(),
            |lc| lc + low0.get_variable(),
        );

        // Higher limb of the less significant uint256
        let low1 = AllocatedNum::alloc(
            cs.namespace(|| "alloc higher limb of lower uint256"),
            || Ok(*res2.get_value().get()? + pow64 * *res3.get_value().get()?),
        )?;
        // Check that low1 is consistent with res2 and res3
        cs.enforce(
            || "check low1 == res2 +  (2^64) * res3",
            |lc| lc + res2.get_variable() + (pow64, res3.get_variable()),
            |lc| lc + CS::one(),
            |lc| lc + low1.get_variable(),
        );

        // Lower limb of the more significant uint256
        let high0 = AllocatedNum::alloc(
            cs.namespace(|| "alloc lower limb of higher uint256"),
            || Ok(*res4.get_value().get()? + pow64 * *res5.get_value().get()?),
        )?;
        // Check that high0 is consistent with res4 and res5
        cs.enforce(
            || "check high0 == res4 +  (2^64) * res5",
            |lc| lc + res4.get_variable() + (pow64, res5.get_variable()),
            |lc| lc + CS::one(),
            |lc| lc + high0.get_variable(),
        );

        // Higher limb of the more significant uint256
        let high1 = AllocatedNum::alloc(
            cs.namespace(|| "alloc higher limb of higher uint256"),
            || Ok(*res6.get_value().get()? + pow64 * *carry.get_value().get()?),
        )?;
        // Check that high1 is consistent with res6 and carry
        cs.enforce(
            || "check high1 == res6 +  (2^64) * carry ",
            |lc| lc + res6.get_variable() + (pow64, carry.get_variable()),
            |lc| lc + CS::one(),
            |lc| lc + high1.get_variable(),
        );

        let pow256_bigint = BigUint::from(1u8) << 256;
        let low_value_bigint = a.value.as_ref().and_then(|a_val| {
            b.value
                .as_ref()
                .and_then(|b_val| Some((a_val * b_val) % &pow256_bigint))
        });
        let high_value_bigint = a.value.as_ref().and_then(|a_val| {
            b.value
                .as_ref()
                .and_then(|b_val| Some((a_val * b_val) / pow256_bigint))
        });

        let low = Uint256 {
            low: low0,
            high: low1,
            value: low_value_bigint,
        };
        let high = Uint256 {
            low: high0,
            high: high1,
            value: high_value_bigint,
        };

        Ok((low, high))
    }

    /// Returns the quotient and remainder as a pair of uint256
    /// variables when `a` is divided by `div`
    pub(crate) fn unsigned_div_rem<CS>(
        mut cs: CS,
        a: &Self,
        div: &Self,
    ) -> Result<(Self, Self), SynthesisError>
    where
        CS: ConstraintSystem<Scalar>,
    {
        let (quotient_bigint, remainder_bigint) = match (a.value.as_ref(), div.value.as_ref()) {
            (Some(a_int), Some(div_int)) => (Some(a_int / div_int), Some(a_int % div_int)),
            (_, _) => (None, None),
        };

        let ones_128_bigint = BigUint::from_bytes_le(&[0xFF; 16]);

        let q_low_bigint = quotient_bigint.as_ref().map(|x| x & &ones_128_bigint);
        let q_high_bigint = quotient_bigint
            .as_ref()
            .map(|x| (x >> 128i32) & &ones_128_bigint);
        let r_low_bigint = remainder_bigint.as_ref().map(|x| x & &ones_128_bigint);
        let r_high_bigint = remainder_bigint
            .as_ref()
            .map(|x| (x >> 128i32) & &ones_128_bigint);

        let biguint_to_u128 = |x: Option<BigUint>| {
            let b = x.map(|v| v.to_bytes_le());
            b.map(|mut v| {
                v.extend_from_slice(&[0u8; 16]);
                v.truncate(16);
                u128::from_le_bytes(v.try_into().unwrap())
            })
        };

        let q_low_u128 = biguint_to_u128(q_low_bigint);
        let q_high_u128 = biguint_to_u128(q_high_bigint);
        let r_low_u128 = biguint_to_u128(r_low_bigint);
        let r_high_u128 = biguint_to_u128(r_high_bigint);

        let q_low_scalar = q_low_u128.map(|x| Scalar::from_u128(x));
        let q_high_scalar = q_high_u128.map(|x| Scalar::from_u128(x));
        let r_low_scalar = r_low_u128.map(|x| Scalar::from_u128(x));
        let r_high_scalar = r_high_u128.map(|x| Scalar::from_u128(x));

        let q_low = AllocatedNum::alloc(cs.namespace(|| "alloc quotient low limb"), || {
            q_low_scalar.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let q_high = AllocatedNum::alloc(cs.namespace(|| "alloc quotient high limb"), || {
            q_high_scalar.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let r_low = AllocatedNum::alloc(cs.namespace(|| "alloc remainder low limb"), || {
            r_low_scalar.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let r_high = AllocatedNum::alloc(cs.namespace(|| "alloc remainder high limb"), || {
            r_high_scalar.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let quotient = Uint256 {
            low: q_low,
            high: q_high,
            value: quotient_bigint,
        };
        let remainder = Uint256 {
            low: r_low,
            high: r_high,
            value: remainder_bigint,
        };

        Self::check_limbs(&quotient, cs.namespace(|| "check quotient limb ranges"))?;
        Self::check_limbs(&remainder, cs.namespace(|| "check remainder limb ranges"))?;

        let (prod_mod2pow256, carry) = Self::mul(
            cs.namespace(|| "multiply quotient and divisor"),
            &quotient,
            &div,
        )?;
        // carry == 0
        Self::enforce_equal_zero(&carry, cs.namespace(|| "check higher 256 bits are zero"))?;

        let (a_calc, add_carry) = Self::add(
            cs.namespace(|| "add prod and remainder"),
            &prod_mod2pow256,
            &remainder,
        )?;

        // a == div*quotient
        Self::enforce_equal(
            cs.namespace(|| "calculated and actual dividend must be equal"),
            &a,
            &a_calc,
        )?;
        // add_carry == false
        Boolean::enforce_equal(
            cs.namespace(|| "check that no carry occurs"),
            &add_carry,
            &Boolean::Constant(false),
        )?;

        let remainder_lt_div =
            Self::less_than(cs.namespace(|| "is remainder < div"), &remainder, &div)?;
        Boolean::enforce_equal(
            cs.namespace(|| "enforce remainder < div"),
            &remainder_lt_div,
            &Boolean::Constant(true),
        )?;

        Ok((quotient, remainder))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bellpepper_core::test_cs::TestConstraintSystem;
    use ff::{Field, PrimeField};
    use pasta_curves::Fp;
    use rand::Rng;
    use rand_core::{RngCore, SeedableRng};
    use rand_xorshift::XorShiftRng;

    #[test]
    fn test_check_limbs() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let low_val: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let high_val: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let low_scalar = Fp::from_u128(low_val);
            let high_scalar = Fp::from_u128(high_val);

            let low =
                AllocatedNum::alloc(cs.namespace(|| format!("alloc low {i}")), || Ok(low_scalar));
            let high = AllocatedNum::alloc(cs.namespace(|| format!("alloc high {i}")), || {
                Ok(high_scalar)
            });

            // value is not checked in check_limbs
            let u = Uint256 {
                low: low.unwrap(),
                high: high.unwrap(),
                value: None,
            };

            let res = u.check_limbs(cs.namespace(|| format!("check uint256 {i}")));
            assert!(res.is_ok())
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 256 * num_tests);
    }

    #[test]
    fn test_fe_to_uint256() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let fe_val = Fp::random(&mut rng);
            let fe = AllocatedNum::alloc(cs.namespace(|| format!("alloc fe {i}")), || Ok(fe_val));
            assert!(fe.is_ok());

            let u = Uint256::field_element_to_uint256(
                cs.namespace(|| format!("uint256 {i}")),
                &fe.unwrap(),
            );
            assert!(u.is_ok());

            let u = u.unwrap();
            let pow128 = Fp::from_u128(u128::MAX) + Fp::ONE;

            let u_val = u.low.get_value().unwrap() + u.high.get_value().unwrap() * pow128;
            assert_eq!(u_val, fe_val);
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 303 * num_tests);
    }

    #[test]
    fn test_uint256_to_fe() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let fe_val = Fp::random(&mut rng);
            let fe = AllocatedNum::alloc(cs.namespace(|| format!("alloc fe {i}")), || Ok(fe_val));
            assert!(fe.is_ok());

            let u = Uint256::field_element_to_uint256(
                cs.namespace(|| format!("uint256 {i}")),
                &fe.unwrap(),
            );
            assert!(u.is_ok());

            let fe_rt = u.as_ref().unwrap().uint256_to_field_element_unchecked(
                cs.namespace(|| format!("alloc round-trip fe {i}")),
            );
            assert!(fe_rt.is_ok());

            assert_eq!(fe_rt.unwrap().get_value().unwrap(), fe_val);
        }
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 304 * num_tests);
    }

    #[test]
    fn test_less_than() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let a_low: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let a_high: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let b_low: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let b_high: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);

            // Unlikely that a_high == b_high, in which case we have to compare a_low and b_low
            let (a_low, a_high, b_low, b_high) = if a_high < b_high {
                (a_low, a_high, b_low, b_high)
            } else {
                (b_low, b_high, a_low, a_high)
            };

            let a_low_scalar = Fp::from_u128(a_low);
            let a_high_scalar = Fp::from_u128(a_high);
            let b_low_scalar = Fp::from_u128(b_low);
            let b_high_scalar = Fp::from_u128(b_high);

            let a_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc a low {i}")), || {
                Ok(a_low_scalar)
            });
            let a_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc a high {i}")), || {
                Ok(a_high_scalar)
            });
            let b_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc b low {i}")), || {
                Ok(b_low_scalar)
            });
            let b_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc b high {i}")), || {
                Ok(b_high_scalar)
            });

            // value is not checked in less_than
            let a = Uint256 {
                low: a_low.unwrap(),
                high: a_high.unwrap(),
                value: None,
            };
            let b = Uint256 {
                low: b_low.unwrap(),
                high: b_high.unwrap(),
                value: None,
            };

            let res = Uint256::less_than(cs.namespace(|| format!("check a < b {i}")), &a, &b);
            assert!(res.is_ok());
            assert_eq!(res.unwrap().get_value().unwrap(), true);
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 267 * num_tests);
    }

    #[test]
    fn test_less_than_or_equal() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let a_low: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let a_high: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let b_low: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let b_high: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);

            // Unlikely that a_high == b_high, in which case we have to compare a_low and b_low
            let (a_low, a_high, b_low, b_high) = if a_high <= b_high {
                (a_low, a_high, b_low, b_high)
            } else {
                (b_low, b_high, a_low, a_high)
            };

            let a_low_scalar = Fp::from_u128(a_low);
            let a_high_scalar = Fp::from_u128(a_high);
            let b_low_scalar = Fp::from_u128(b_low);
            let b_high_scalar = Fp::from_u128(b_high);

            let a_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc a low {i}")), || {
                Ok(a_low_scalar)
            });
            let a_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc a high {i}")), || {
                Ok(a_high_scalar)
            });
            let b_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc b low {i}")), || {
                Ok(b_low_scalar)
            });
            let b_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc b high {i}")), || {
                Ok(b_high_scalar)
            });

            // value is not checked in less_than_or_equal
            let a = Uint256 {
                low: a_low.unwrap(),
                high: a_high.unwrap(),
                value: None,
            };
            let b = Uint256 {
                low: b_low.unwrap(),
                high: b_high.unwrap(),
                value: None,
            };

            let res =
                Uint256::less_than_or_equal(cs.namespace(|| format!("check a <= b {i}")), &a, &b);
            assert!(res.is_ok());
            assert_eq!(res.unwrap().get_value().unwrap(), true);

            let res =
                Uint256::less_than_or_equal(cs.namespace(|| format!("check a <= a {i}")), &a, &a);
            assert!(res.is_ok());
            assert_eq!(res.unwrap().get_value().unwrap(), true);
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 267 * 2 * num_tests);
    }
    #[test]
    fn test_enforce_equal() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let low_val: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let high_val: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let low_scalar = Fp::from_u128(low_val);
            let high_scalar = Fp::from_u128(high_val);

            let low =
                AllocatedNum::alloc(cs.namespace(|| format!("alloc low {i}")), || Ok(low_scalar));
            let high = AllocatedNum::alloc(cs.namespace(|| format!("alloc high {i}")), || {
                Ok(high_scalar)
            });

            // value is not checked in enforce_equal
            let u = Uint256 {
                low: low.unwrap(),
                high: high.unwrap(),
                value: None,
            };

            let res =
                Uint256::enforce_equal(cs.namespace(|| format!("check equality {i}")), &u, &u);
            assert!(res.is_ok())
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2 * num_tests);
    }

    #[test]
    fn test_enforce_equal_zero() {
        let mut cs = TestConstraintSystem::<Fp>::new();

        let low = AllocatedNum::alloc(cs.namespace(|| "alloc low zero"), || Ok(Fp::ZERO));
        let high = AllocatedNum::alloc(cs.namespace(|| "alloc high zero"), || Ok(Fp::ZERO));

        // value is not used in enforce_equal_zero
        let u = Uint256 {
            low: low.unwrap(),
            high: high.unwrap(),
            value: None,
        };

        let res = u.enforce_equal_zero(cs.namespace(|| "check equality with zero"));
        assert!(res.is_ok());

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2);
    }

    #[test]
    fn test_not() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let low_val: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let high_val: u128 = ((rng.next_u64() as u128) << 64) | (rng.next_u64() as u128);
            let low_scalar = Fp::from_u128(low_val);
            let high_scalar = Fp::from_u128(high_val);

            let low =
                AllocatedNum::alloc(cs.namespace(|| format!("alloc low {i}")), || Ok(low_scalar));
            let high = AllocatedNum::alloc(cs.namespace(|| format!("alloc high {i}")), || {
                Ok(high_scalar)
            });

            // value is not checked in check_limbs
            let u = Uint256 {
                low: low.unwrap(),
                high: high.unwrap(),
                value: None,
            };

            let res = u.not(cs.namespace(|| format!("compute not {i}")));
            assert!(res.is_ok());
            let not_u = res.unwrap();

            let low_val_not = !low_val;
            let high_val_not = !high_val;
            let low_scalar_not = Fp::from_u128(low_val_not);
            let high_scalar_not = Fp::from_u128(high_val_not);

            assert_eq!(not_u.low.get_value().unwrap(), low_scalar_not);
            assert_eq!(not_u.high.get_value().unwrap(), high_scalar_not);
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2 * num_tests);
    }

    #[test]
    fn test_add() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let a_bytes: [u8; 32] = rng.gen();
            let b_bytes: [u8; 32] = rng.gen();

            let a_biguint = BigUint::from_bytes_le(&a_bytes);
            let b_biguint = BigUint::from_bytes_le(&b_bytes);
            let pow256 = BigUint::from(true) << 256;
            let sum_biguint = &a_biguint + &b_biguint;
            let sum_modulo_2pow256 = &sum_biguint % &pow256;
            let carry = sum_biguint > pow256;

            let a_low_u128: u128 = u128::from_le_bytes(a_bytes[0..16].try_into().unwrap());
            let a_high_u128: u128 = u128::from_le_bytes(a_bytes[16..].try_into().unwrap());
            let b_low_u128: u128 = u128::from_le_bytes(b_bytes[0..16].try_into().unwrap());
            let b_high_u128: u128 = u128::from_le_bytes(b_bytes[16..].try_into().unwrap());

            let a_low_scalar = Fp::from_u128(a_low_u128);
            let a_high_scalar = Fp::from_u128(a_high_u128);
            let b_low_scalar = Fp::from_u128(b_low_u128);
            let b_high_scalar = Fp::from_u128(b_high_u128);

            let a_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc a low {i}")), || {
                Ok(a_low_scalar)
            });
            let a_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc a high {i}")), || {
                Ok(a_high_scalar)
            });
            let b_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc b low {i}")), || {
                Ok(b_low_scalar)
            });
            let b_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc b high {i}")), || {
                Ok(b_high_scalar)
            });

            let a = Uint256 {
                low: a_low.unwrap(),
                high: a_high.unwrap(),
                value: Some(a_biguint),
            };
            let b = Uint256 {
                low: b_low.unwrap(),
                high: b_high.unwrap(),
                value: Some(b_biguint),
            };

            let res = Uint256::add(cs.namespace(|| format!("compute a + b {i}")), &a, &b);
            assert!(res.is_ok());
            let (sum, c) = res.unwrap();

            assert_eq!(sum.value.unwrap(), sum_modulo_2pow256);
            assert_eq!(c.get_value().unwrap(), carry);

            let ones_128_bigint = BigUint::from_bytes_le(&[0xFF; 16]);
            let sum_low_scalar = Fp::from_u128(u128::from_le_bytes(
                (&sum_biguint & &ones_128_bigint)
                    .to_bytes_le()
                    .try_into()
                    .unwrap(),
            ));
            let sum_high_scalar = Fp::from_u128(u128::from_le_bytes(
                ((sum_biguint >> 128i32) & &ones_128_bigint)
                    .to_bytes_le()
                    .try_into()
                    .unwrap(),
            ));
            assert_eq!(sum.low.get_value().unwrap(), sum_low_scalar);
            assert_eq!(sum.high.get_value().unwrap(), sum_high_scalar);
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 260 * num_tests);
    }

    #[test]
    fn test_mul() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let a_bytes: [u8; 32] = rng.gen();
            let b_bytes: [u8; 32] = rng.gen();

            let a_biguint = BigUint::from_bytes_le(&a_bytes);
            let b_biguint = BigUint::from_bytes_le(&b_bytes);
            let prod_biguint = &a_biguint * &b_biguint;

            let a_low_u128: u128 = u128::from_le_bytes(a_bytes[0..16].try_into().unwrap());
            let a_high_u128: u128 = u128::from_le_bytes(a_bytes[16..].try_into().unwrap());
            let b_low_u128: u128 = u128::from_le_bytes(b_bytes[0..16].try_into().unwrap());
            let b_high_u128: u128 = u128::from_le_bytes(b_bytes[16..].try_into().unwrap());

            let a_low_scalar = Fp::from_u128(a_low_u128);
            let a_high_scalar = Fp::from_u128(a_high_u128);
            let b_low_scalar = Fp::from_u128(b_low_u128);
            let b_high_scalar = Fp::from_u128(b_high_u128);

            let a_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc a low {i}")), || {
                Ok(a_low_scalar)
            });
            let a_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc a high {i}")), || {
                Ok(a_high_scalar)
            });
            let b_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc b low {i}")), || {
                Ok(b_low_scalar)
            });
            let b_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc b high {i}")), || {
                Ok(b_high_scalar)
            });

            let a = Uint256 {
                low: a_low.unwrap(),
                high: a_high.unwrap(),
                value: Some(a_biguint),
            };
            let b = Uint256 {
                low: b_low.unwrap(),
                high: b_high.unwrap(),
                value: Some(b_biguint),
            };

            let res = Uint256::mul(cs.namespace(|| format!("compute a * b {i}")), &a, &b);
            assert!(res.is_ok());
            let (prod0, prod1) = res.unwrap();

            let mut prod_bytes = prod_biguint.to_bytes_le();
            prod_bytes.extend_from_slice(&[0u8; 64]);
            prod_bytes.truncate(64);

            let prod0_low_scalar =
                Fp::from_u128(u128::from_le_bytes(prod_bytes[0..16].try_into().unwrap()));
            let prod0_high_scalar =
                Fp::from_u128(u128::from_le_bytes(prod_bytes[16..32].try_into().unwrap()));
            let prod1_low_scalar =
                Fp::from_u128(u128::from_le_bytes(prod_bytes[32..48].try_into().unwrap()));
            let prod1_high_scalar =
                Fp::from_u128(u128::from_le_bytes(prod_bytes[48..].try_into().unwrap()));

            assert_eq!(prod0.low.get_value().unwrap(), prod0_low_scalar);
            assert_eq!(prod0.high.get_value().unwrap(), prod0_high_scalar);
            assert_eq!(prod1.low.get_value().unwrap(), prod1_low_scalar);
            assert_eq!(prod1.high.get_value().unwrap(), prod1_high_scalar);

            let prod0_biguint = BigUint::from_bytes_le(&prod_bytes[0..32]);
            let prod1_biguint = BigUint::from_bytes_le(&prod_bytes[32..]);
            assert_eq!(prod0.value.unwrap(), prod0_biguint);
            assert_eq!(prod1.value.unwrap(), prod1_biguint);
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 2180 * num_tests);
    }

    #[test]
    fn test_unsigned_div_rem() {
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x3d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        let mut cs = TestConstraintSystem::<Fp>::new();
        let num_tests = 16;

        for i in 0..num_tests {
            let a_bytes: [u8; 32] = rng.gen();
            let div_bytes: [u8; 32] = rng.gen();

            let a_biguint = BigUint::from_bytes_le(&a_bytes);
            let div_biguint = BigUint::from_bytes_le(&div_bytes);
            let quotient_biguint = &a_biguint / &div_biguint;
            let remainder_biguint = &a_biguint % &div_biguint;

            let a_low_u128: u128 = u128::from_le_bytes(a_bytes[0..16].try_into().unwrap());
            let a_high_u128: u128 = u128::from_le_bytes(a_bytes[16..].try_into().unwrap());
            let div_low_u128: u128 = u128::from_le_bytes(div_bytes[0..16].try_into().unwrap());
            let div_high_u128: u128 = u128::from_le_bytes(div_bytes[16..].try_into().unwrap());

            let a_low_scalar = Fp::from_u128(a_low_u128);
            let a_high_scalar = Fp::from_u128(a_high_u128);
            let div_low_scalar = Fp::from_u128(div_low_u128);
            let div_high_scalar = Fp::from_u128(div_high_u128);

            let a_low = AllocatedNum::alloc(cs.namespace(|| format!("alloc a low {i}")), || {
                Ok(a_low_scalar)
            });
            let a_high = AllocatedNum::alloc(cs.namespace(|| format!("alloc a high {i}")), || {
                Ok(a_high_scalar)
            });
            let div_low =
                AllocatedNum::alloc(cs.namespace(|| format!("alloc div low {i}")), || {
                    Ok(div_low_scalar)
                });
            let div_high =
                AllocatedNum::alloc(cs.namespace(|| format!("alloc div high {i}")), || {
                    Ok(div_high_scalar)
                });

            let a = Uint256 {
                low: a_low.unwrap(),
                high: a_high.unwrap(),
                value: Some(a_biguint),
            };
            let div = Uint256 {
                low: div_low.unwrap(),
                high: div_high.unwrap(),
                value: Some(div_biguint),
            };

            let res = Uint256::unsigned_div_rem(
                cs.namespace(|| format!("compute a divided by div {i}")),
                &a,
                &div,
            );
            assert!(res.is_ok());
            let (quotient, remainder) = res.unwrap();

            assert_eq!(quotient.value.unwrap(), quotient_biguint);
            assert_eq!(remainder.value.unwrap(), remainder_biguint);

            let mut quotient_bytes = quotient_biguint.to_bytes_le();
            quotient_bytes.extend_from_slice(&[0u8; 32]);
            quotient_bytes.truncate(32);
            let mut remainder_bytes = remainder_biguint.to_bytes_le();
            remainder_bytes.extend_from_slice(&[0u8; 32]);
            remainder_bytes.truncate(32);

            let quotient_low_scalar = Fp::from_u128(u128::from_le_bytes(
                quotient_bytes[0..16].try_into().unwrap(),
            ));
            let quotient_high_scalar = Fp::from_u128(u128::from_le_bytes(
                quotient_bytes[16..32].try_into().unwrap(),
            ));
            let remainder_low_scalar = Fp::from_u128(u128::from_le_bytes(
                remainder_bytes[0..16].try_into().unwrap(),
            ));
            let remainder_high_scalar = Fp::from_u128(u128::from_le_bytes(
                remainder_bytes[16..].try_into().unwrap(),
            ));

            assert_eq!(quotient.low.get_value().unwrap(), quotient_low_scalar);
            assert_eq!(quotient.high.get_value().unwrap(), quotient_high_scalar);
            assert_eq!(remainder.low.get_value().unwrap(), remainder_low_scalar);
            assert_eq!(remainder.high.get_value().unwrap(), remainder_high_scalar);
        }

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 3225 * num_tests);
    }
}
