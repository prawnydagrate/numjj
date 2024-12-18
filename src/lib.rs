use std::fmt::{self, write};

pub type Base = u64;

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone)]
pub struct Uint<const DIGITS: usize = 2>([Base; DIGITS]);

impl<const DIGITS: usize> Uint<DIGITS> {
    /// The number of bits of memory that this `Uint` type occupies.
    pub const BITS: usize = Base::BITS as usize * DIGITS;

    /// Returns zero. **Panics** if `DIGITS` is less than 1.
    pub fn zero() -> Self {
        assert!(DIGITS > 0);
        Self([0; DIGITS])
    }

    /// Returns one. **Panics** if `DIGITS` is less than 1.
    pub fn one() -> Self {
        assert!(DIGITS > 0);
        let mut one = [0; DIGITS];
        one[0] = 1;
        Self(one)
    }

    /// Implementation of [Donald Ervin Knuth's "Algorithm D"](https://skanthak.hier-im-netz.de/division.html)
    /// for division. **Panics** if `DIGITS` or `RHS_DIGITS` is less than 1.
    fn algd<const RHS_DIGITS: usize>(&self, rhs: &Uint<RHS_DIGITS>) {
        const b: u128 = 2_u128.pow(Base::BITS); // 2^64 doesn't fit in a u64 (range is 0..=(2^64-1))
        assert!(DIGITS > 0 && RHS_DIGITS > 0);
        let (m, n) = (DIGITS, RHS_DIGITS);
        assert!(m + n >= n);
        let mut q = vec![0; m - n + 1]; // (m-n+1)-word quotient
        let mut r = vec![0; n]; // n-word remainder
        let (u, v) = (&self.0, &rhs.0); // m-word dividend, n-word divisor

        // TODO
        todo!()
    }
}

impl<const DIGITS: usize> std::ops::Add<&Uint<DIGITS>> for Uint<DIGITS> {
    type Output = Option<Self>;

    /// Adds two `Uint`s, returning `None` if overflow occurs.
    fn add(mut self, rhs: &Self) -> Self::Output {
        // NOTE: Assuming that both Uints have DIGITS > 0
        let mut carry = 0;
        for x in 0..DIGITS {
            let (l, r) = (self.0[x], rhs.0[x]);
            if (l, r) == (0, 0) {
                if carry > 0 {
                    self.0[x] = carry;
                    carry = 0;
                }
                break;
            }
            match l.checked_add(r) {
                Some(sum) => match sum.checked_add(carry) {
                    Some(full) => {
                        self.0[x] = full;
                        carry = 0;
                    }
                    None => {
                        self.0[x] = Base::MAX;
                        carry -= Base::MAX - sum;
                    }
                },
                None => {
                    self.0[x] = Base::MAX;
                    carry += r - (Base::MAX - l);
                }
            };
        }
        if carry > 0 {
            None
        } else {
            Some(self)
        }
    }
}

impl<const DIGITS: usize> From<u8> for Uint<DIGITS> {
    /// Converts a `u8` into a `Uint`. **Panics** if `DIGITS` is less than 1.
    fn from(n: u8) -> Self {
        assert!(DIGITS > 0);
        // NOTE: ASSUMES that u8 is <= Base in size
        let mut arr = [0; DIGITS];
        arr[0] = n as Base;
        Self(arr)
    }
}

impl<const DIGITS: usize> From<u16> for Uint<DIGITS> {
    /// Converts a `u16` into a `Uint`. **Panics** if `DIGITS` is less than 1.
    fn from(n: u16) -> Self {
        assert!(DIGITS > 0);
        // NOTE: ASSUMES that u16 is <= Base in size
        let mut arr = [0; DIGITS];
        arr[0] = n as Base;
        Self(arr)
    }
}

impl<const DIGITS: usize> From<u32> for Uint<DIGITS> {
    /// Converts a `u32` into a `Uint`. **Panics** if `DIGITS` is less than 1.
    fn from(n: u32) -> Self {
        assert!(DIGITS > 0);
        // NOTE: ASSUMES that u32 is <= Base in size
        let mut arr = [0; DIGITS];
        arr[0] = n as Base;
        Self(arr)
    }
}

impl<const DIGITS: usize> From<usize> for Uint<DIGITS> {
    /// Converts a `usize` into a `Uint`. **Panics** if `DIGITS` is less than 1.
    fn from(n: usize) -> Self {
        assert!(DIGITS > 0);
        // NOTE: ASSUMES that usize is <= Base in size
        let mut arr = [0; DIGITS];
        arr[0] = n as Base;
        Self(arr)
    }
}

impl<const DIGITS: usize> From<u64> for Uint<DIGITS> {
    /// Converts a `u64` into a `Uint`. **Panics** if `DIGITS` is less than 1.
    fn from(n: u64) -> Self {
        assert!(DIGITS > 0);
        // NOTE: ASSUMES that u64 is <= Base in size
        let mut arr = [0; DIGITS];
        arr[0] = n as Base;
        Self(arr)
    }
}

impl<const DIGITS: usize> From<u128> for Uint<DIGITS> {
    /// Converts a `u128` into a `Uint`. **Panics** if `DIGITS` is less than 1.
    fn from(n: u128) -> Self {
        assert!(DIGITS > 0);
        // TODO
        todo!()
    }
}

impl<const DIGITS: usize> fmt::Display for Uint<DIGITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        // TODO: convert base (2^128) number to base 10 string
        write!(f, "{s}")
    }
}
