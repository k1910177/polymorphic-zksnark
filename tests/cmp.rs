use ark_ff::Field;
use ark_r1cs_std::{prelude::{Boolean, EqGadget}, R1CSVar, uint8::UInt8, ToBitsGadget};
use ark_relations::r1cs::SynthesisError;

pub trait CmpGadget<ConstraintF: Field>: R1CSVar<ConstraintF> + EqGadget<ConstraintF> {
    #[inline]
    fn is_geq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        // self >= other => self == other || self > other
        //               => !(self < other)
        self.is_lt(other).map(|b| b.not())
    }

    #[inline]
    fn is_leq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        // self <= other => self == other || self < other
        //               => self == other || other > self
        //               => self >= other
        other.is_geq(self)
    }

    #[inline]
    fn is_gt(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        // self > other => !(self == other  || self < other)
        //              => !(self <= other)
        self.is_leq(other).map(|b| b.not())
    }

    fn is_lt(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError>;
}

impl<ConstraintF: Field> CmpGadget<ConstraintF> for UInt8<ConstraintF> {
    fn is_lt(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        // Determine the variable mode.
        if self.is_constant() && other.is_constant() {
            let self_value = self.value().unwrap();
            let other_value = other.value().unwrap();
            let result = Boolean::constant(self_value < other_value);
            Ok(result)
        } else {
            let diff_bits = self.xor(other)?.to_bits_be()?.into_iter();
            let mut result = Boolean::FALSE;
            let mut a_and_b_equal_so_far = Boolean::TRUE;
            let a_bits = self.to_bits_be()?;
            let b_bits = other.to_bits_be()?;
            for ((a_and_b_are_unequal, a), b) in diff_bits.zip(a_bits).zip(b_bits) {
                let a_is_lt_b = a.not().and(&b)?;
                let a_and_b_are_equal = a_and_b_are_unequal.not();
                result = result.or(&a_is_lt_b.and(&a_and_b_equal_so_far)?)?;
                a_and_b_equal_so_far = a_and_b_equal_so_far.and(&a_and_b_are_equal)?;
            }
            Ok(result)
        }
    }
}