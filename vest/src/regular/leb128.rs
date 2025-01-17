use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Unsigned LEB128
pub struct UnsignedLEB128;

/// Result of UnsignedLEB128
pub type UInt = u64;

impl View for UnsignedLEB128 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        Self
    }
}

/// Byte size of UInt
#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }
pub(super) use uint_size;

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
}
pub(crate) use is_high_8_bit_set;

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}
pub(crate) use take_low_7_bits;

/// Set the highest bit to 1 as an u8
#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}
pub(super) use set_high_8_bit;

/// Max value for an n-bit unsigned integer
#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}
pub(super) use n_bit_max_unsigned;

impl SpecCombinator for UnsignedLEB128 {
    type Type = UInt;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()>
        decreases s.len()
    {
        let v = take_low_7_bits!(s.first());

        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                match self.spec_parse(s.drop_first()) {
                    Ok((n, v2)) =>
                        // Check for overflow and canonicity (v2 should not be 0)
                        if n < usize::MAX && 0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                            Ok(((n + 1) as usize, v2 << 7 | v as Self::Type))
                        } else {
                            Err(())
                        }

                    Err(e) => Err(e),
                }
            } else {
                Ok((1, v as Self::Type))
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>)
        decreases s.len()
    {
        if s.len() != 0 {
            self.spec_parse_wf(s.drop_first());
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()>
    {
        Self::spec_serialize_helper(v)
    }
}

impl UnsignedLEB128 {
    /// Helper function for spec_serialize
    pub open spec fn spec_serialize_helper(v: UInt) -> Result<Seq<u8>, ()>
        decreases v via Self::spec_serialize_dereases
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            Ok(seq![lo])
        } else {
            match Self::spec_serialize_helper(hi) {
                Ok(s) => Ok(seq![set_high_8_bit!(lo)] + s),
                Err(e) => Err(e),
            }
        }
    }

    #[via_fn]
    proof fn spec_serialize_dereases(v: UInt)
    {
        assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
    }

    proof fn lemma_spec_serialize_length(&self, v: UInt)
        ensures self.spec_serialize(v) matches Ok(s) ==> s.len() <= 10
    {
        reveal_with_fuel(UnsignedLEB128::spec_serialize_helper, 10);
        assert(
            v >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 == 0
        ) by (bit_vector);
    }
}

impl SecureSpecCombinator for UnsignedLEB128 {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        assume(false);
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        decreases v
    {
        if let Ok(s) = self.spec_serialize(v) {
            let lo = take_low_7_bits!(v);
            let hi = v >> 7;

            self.lemma_spec_serialize_length(v);

            assert({
                &&& !is_high_8_bit_set!(take_low_7_bits!(v))
                &&& v >> 7 == 0 ==> v == take_low_7_bits!(v)
                &&& v >> 7 != 0 ==> v >> 7 < v
                &&& is_high_8_bit_set!(set_high_8_bit!(lo))
                &&& (v >> 7) << 7 | take_low_7_bits!(v) as UInt == v
                &&& (v >> 7) <= n_bit_max_unsigned!(8 * uint_size!() - 7)
                &&& take_low_7_bits!(set_high_8_bit!(take_low_7_bits!(v))) == take_low_7_bits!(v)
            }) by (bit_vector);

            if hi != 0 {
                self.theorem_serialize_parse_roundtrip(hi);

                let hi_bytes = self.spec_serialize(hi).unwrap();
                assert(s.drop_first() == hi_bytes);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        assume(false);
    }
}

}
