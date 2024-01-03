use core::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

use crate::{Symbol, SymbolOverflowError};

impl From<u8> for Symbol {
    #[inline]
    fn from(id: u8) -> Self {
        Self(id.into())
    }
}

impl From<NonZeroU8> for Symbol {
    #[inline]
    fn from(sym: NonZeroU8) -> Self {
        Self(sym.get().into())
    }
}

impl From<u16> for Symbol {
    #[inline]
    fn from(id: u16) -> Self {
        Self(id.into())
    }
}

impl From<NonZeroU16> for Symbol {
    #[inline]
    fn from(sym: NonZeroU16) -> Self {
        Self(sym.get().into())
    }
}

impl From<u32> for Symbol {
    #[inline]
    fn from(id: u32) -> Self {
        Self(id)
    }
}

impl From<NonZeroU32> for Symbol {
    #[inline]
    fn from(sym: NonZeroU32) -> Self {
        Self(sym.get())
    }
}

impl TryFrom<u64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value)?;
        Ok(id.into())
    }
}

impl TryFrom<NonZeroU64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: NonZeroU64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl TryFrom<usize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value)?;
        Ok(id.into())
    }
}

impl TryFrom<NonZeroUsize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: NonZeroUsize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl From<&u8> for Symbol {
    #[inline]
    fn from(id: &u8) -> Self {
        Self((*id).into())
    }
}

impl From<&NonZeroU8> for Symbol {
    #[inline]
    fn from(sym: &NonZeroU8) -> Self {
        Self(sym.get().into())
    }
}

impl From<&u16> for Symbol {
    #[inline]
    fn from(id: &u16) -> Self {
        Self((*id).into())
    }
}

impl From<&NonZeroU16> for Symbol {
    #[inline]
    fn from(sym: &NonZeroU16) -> Self {
        Self(sym.get().into())
    }
}

impl From<&u32> for Symbol {
    #[inline]
    fn from(id: &u32) -> Self {
        Self(*id)
    }
}

impl From<&NonZeroU32> for Symbol {
    #[inline]
    fn from(sym: &NonZeroU32) -> Self {
        Self(sym.get())
    }
}

impl TryFrom<&u64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: &u64) -> Result<Self, Self::Error> {
        let id = u32::try_from(*value)?;
        Ok(id.into())
    }
}

impl TryFrom<&NonZeroU64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: &NonZeroU64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl TryFrom<&usize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: &usize) -> Result<Self, Self::Error> {
        let id = u32::try_from(*value)?;
        Ok(id.into())
    }
}

impl TryFrom<&NonZeroUsize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(value: &NonZeroUsize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl From<Symbol> for u32 {
    #[inline]
    fn from(sym: Symbol) -> Self {
        sym.id()
    }
}

impl From<Symbol> for u64 {
    #[inline]
    fn from(sym: Symbol) -> Self {
        sym.id().into()
    }
}

impl From<Symbol> for usize {
    #[inline]
    fn from(sym: Symbol) -> Self {
        // Ensure this cast is lossless.
        const_assert!(usize::BITS >= u32::BITS);

        sym.id() as usize
    }
}

impl From<Symbol> for i64 {
    #[inline]
    fn from(sym: Symbol) -> Self {
        sym.id().into()
    }
}

impl From<&Symbol> for u32 {
    #[inline]
    fn from(sym: &Symbol) -> Self {
        sym.id()
    }
}

impl From<&Symbol> for u64 {
    #[inline]
    fn from(sym: &Symbol) -> Self {
        sym.id().into()
    }
}

impl From<&Symbol> for usize {
    #[inline]
    fn from(sym: &Symbol) -> Self {
        (*sym).into()
    }
}

impl From<&Symbol> for i64 {
    #[inline]
    fn from(sym: &Symbol) -> Self {
        sym.id().into()
    }
}

#[cfg(test)]
mod tests {
    use core::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

    use crate::Symbol;

    #[test]
    fn symbol_from_primitive() {
        assert_eq!(Symbol::from(0_u8), Symbol::new(0));
        assert_eq!(Symbol::from(17_u8), Symbol::new(17));

        assert_eq!(Symbol::from(0_u16), Symbol::new(0));
        assert_eq!(Symbol::from(17_u16), Symbol::new(17));

        assert_eq!(Symbol::from(0_u32), Symbol::new(0));
        assert_eq!(Symbol::from(17_u32), Symbol::new(17));

        assert_eq!(Symbol::try_from(0_u64).unwrap(), Symbol::new(0));
        assert_eq!(Symbol::try_from(17_u64).unwrap(), Symbol::new(17));

        Symbol::try_from(u64::MAX).unwrap_err();
        Symbol::try_from(u64::from(u32::MAX) + 1).unwrap_err();

        assert_eq!(Symbol::try_from(0_usize).unwrap(), Symbol::new(0));
        assert_eq!(Symbol::try_from(17_usize).unwrap(), Symbol::new(17));

        #[cfg(target_pointer_width = "64")]
        {
            Symbol::try_from(usize::MAX).unwrap_err();
            Symbol::try_from(u64::from(u32::MAX) + 1).unwrap_err();
        }
    }

    #[test]
    fn symbol_from_primitive_ref() {
        assert_eq!(Symbol::from(&0_u8), Symbol::new(0));
        assert_eq!(Symbol::from(&17_u8), Symbol::new(17));

        assert_eq!(Symbol::from(&0_u16), Symbol::new(0));
        assert_eq!(Symbol::from(&17_u16), Symbol::new(17));

        assert_eq!(Symbol::from(&0_u32), Symbol::new(0));
        assert_eq!(Symbol::from(&17_u32), Symbol::new(17));

        assert_eq!(Symbol::try_from(&0_u64).unwrap(), Symbol::new(0));
        assert_eq!(Symbol::try_from(&17_u64).unwrap(), Symbol::new(17));

        Symbol::try_from(&u64::MAX).unwrap_err();
        Symbol::try_from(&(u64::from(u32::MAX) + 1)).unwrap_err();

        assert_eq!(Symbol::try_from(&0_usize).unwrap(), Symbol::new(0));
        assert_eq!(Symbol::try_from(&17_usize).unwrap(), Symbol::new(17));

        #[cfg(target_pointer_width = "64")]
        {
            Symbol::try_from(&usize::MAX).unwrap_err();
            Symbol::try_from(&(u64::from(u32::MAX) + 1)).unwrap_err();
        }
    }

    #[test]
    fn symbol_from_nonzero() {
        assert_eq!(
            Symbol::from(NonZeroU8::new(17_u8).unwrap()),
            Symbol::new(17)
        );

        assert_eq!(
            Symbol::from(NonZeroU16::new(17_u16).unwrap()),
            Symbol::new(17)
        );

        assert_eq!(
            Symbol::from(NonZeroU32::new(17_u32).unwrap()),
            Symbol::new(17)
        );

        assert_eq!(
            Symbol::try_from(NonZeroU64::new(17_u64).unwrap()).unwrap(),
            Symbol::new(17)
        );

        Symbol::try_from(NonZeroU64::new(u64::MAX).unwrap()).unwrap_err();
        Symbol::try_from(NonZeroU64::new(u64::from(u32::MAX) + 1).unwrap()).unwrap_err();

        assert_eq!(
            Symbol::try_from(NonZeroUsize::new(17_usize).unwrap()).unwrap(),
            Symbol::new(17)
        );

        #[cfg(target_pointer_width = "64")]
        {
            Symbol::try_from(NonZeroUsize::new(usize::MAX).unwrap()).unwrap_err();
            Symbol::try_from(NonZeroUsize::new((usize::try_from(u32::MAX).unwrap()) + 1).unwrap())
                .unwrap_err();
        }
    }

    #[test]
    fn symbol_from_nonzero_ref() {
        assert_eq!(
            Symbol::from(&NonZeroU8::new(17_u8).unwrap()),
            Symbol::new(17)
        );

        assert_eq!(
            Symbol::from(&NonZeroU16::new(17_u16).unwrap()),
            Symbol::new(17)
        );

        assert_eq!(
            Symbol::from(&NonZeroU32::new(17_u32).unwrap()),
            Symbol::new(17)
        );

        assert_eq!(
            Symbol::try_from(&NonZeroU64::new(17_u64).unwrap()).unwrap(),
            Symbol::new(17)
        );

        Symbol::try_from(&NonZeroU64::new(u64::MAX).unwrap()).unwrap_err();
        Symbol::try_from(&NonZeroU64::new(u64::from(u32::MAX) + 1).unwrap()).unwrap_err();

        assert_eq!(
            Symbol::try_from(&NonZeroUsize::new(17_usize).unwrap()).unwrap(),
            Symbol::new(17)
        );

        #[cfg(target_pointer_width = "64")]
        {
            Symbol::try_from(&NonZeroUsize::new(usize::MAX).unwrap()).unwrap_err();
            Symbol::try_from(&NonZeroUsize::new((usize::try_from(u32::MAX).unwrap()) + 1).unwrap())
                .unwrap_err();
        }
    }

    #[test]
    fn symbol_into_u32_eql_symbol_as_id() {
        let test_cases = [0, 1, 17, 192, u32::MAX];
        for id in test_cases {
            let sym = Symbol::new(id);
            assert_eq!(u32::from(sym), id);
            assert_eq!(u32::from(&sym), id);
            assert_eq!(u32::from(sym), sym.id());
            assert_eq!(u32::from(&sym), sym.id());
        }
    }

    #[test]
    fn primitive_from_symbol() {
        assert_eq!(0_u32, u32::from(Symbol::new(0)));
        assert_eq!(17_u32, u32::from(Symbol::new(17)));

        assert_eq!(0_u64, u64::from(Symbol::new(0)));
        assert_eq!(17_u64, u64::from(Symbol::new(17)));

        assert_eq!(0_usize, usize::from(Symbol::new(0)));
        assert_eq!(17_usize, usize::from(Symbol::new(17)));

        assert_eq!(0_i64, i64::from(Symbol::new(0)));
        assert_eq!(17_i64, i64::from(Symbol::new(17)));
    }

    #[test]
    fn primitive_from_symbol_ref() {
        assert_eq!(0_u32, u32::from(&Symbol::new(0)));
        assert_eq!(17_u32, u32::from(&Symbol::new(17)));

        assert_eq!(0_u64, u64::from(&Symbol::new(0)));
        assert_eq!(17_u64, u64::from(&Symbol::new(17)));

        assert_eq!(0_usize, usize::from(&Symbol::new(0)));
        assert_eq!(17_usize, usize::from(&Symbol::new(17)));

        assert_eq!(0_i64, i64::from(&Symbol::new(0)));
        assert_eq!(17_i64, i64::from(&Symbol::new(17)));
    }
}
