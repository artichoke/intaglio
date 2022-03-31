use core::convert::TryFrom;
use core::mem::size_of;
use core::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize};

use crate::{Symbol, SymbolOverflowError};

impl From<u8> for Symbol {
    #[inline]
    fn from(sym: u8) -> Self {
        // Safety:
        //
        // `u8::MAX` is less than `u32::MAX`
        unsafe { Self::new_unchecked(sym.into()) }
    }
}

impl From<NonZeroU8> for Symbol {
    #[inline]
    fn from(sym: NonZeroU8) -> Self {
        // Safety:
        //
        // `u8::MAX` is less than `u32::MAX`
        unsafe { Self::new_unchecked(sym.get().into()) }
    }
}

impl From<u16> for Symbol {
    #[inline]
    fn from(sym: u16) -> Self {
        // Safety:
        //
        // `u16::MAX` is less than `u32::MAX`
        unsafe { Self::new_unchecked(sym.into()) }
    }
}

impl From<NonZeroU16> for Symbol {
    #[inline]
    fn from(sym: NonZeroU16) -> Self {
        // Safety:
        //
        // `u16::MAX` is less than `u32::MAX`
        unsafe { Self::new_unchecked(sym.get().into()) }
    }
}

impl TryFrom<u32> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: u32) -> Result<Self, Self::Error> {
        let sym = Self::new(sym).ok_or_else(SymbolOverflowError::new)?;
        Ok(sym)
    }
}

impl TryFrom<NonZeroU32> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: NonZeroU32) -> Result<Self, Self::Error> {
        let sym = Self::new(sym.get()).ok_or_else(SymbolOverflowError::new)?;
        Ok(sym)
    }
}

impl TryFrom<u64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: u64) -> Result<Self, Self::Error> {
        let sym = u32::try_from(sym)?;
        let sym = Self::new(sym).ok_or_else(SymbolOverflowError::new)?;
        Ok(sym)
    }
}

impl TryFrom<NonZeroU64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: NonZeroU64) -> Result<Self, Self::Error> {
        let sym = u32::try_from(sym.get())?;
        let sym = Self::new(sym).ok_or_else(SymbolOverflowError::new)?;
        Ok(sym)
    }
}

impl TryFrom<usize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: usize) -> Result<Self, Self::Error> {
        let sym = u32::try_from(sym)?;
        let sym = Self::new(sym).ok_or_else(SymbolOverflowError::new)?;
        Ok(sym)
    }
}

impl TryFrom<NonZeroUsize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: NonZeroUsize) -> Result<Self, Self::Error> {
        let sym = u32::try_from(sym.get())?;
        let sym = Self::new(sym).ok_or_else(SymbolOverflowError::new)?;
        Ok(sym)
    }
}

impl From<&u8> for Symbol {
    #[inline]
    fn from(sym: &u8) -> Self {
        (*sym).into()
    }
}

impl From<&NonZeroU8> for Symbol {
    #[inline]
    fn from(sym: &NonZeroU8) -> Self {
        sym.get().into()
    }
}

impl From<&u16> for Symbol {
    #[inline]
    fn from(sym: &u16) -> Self {
        (*sym).into()
    }
}

impl From<&NonZeroU16> for Symbol {
    #[inline]
    fn from(sym: &NonZeroU16) -> Self {
        sym.get().into()
    }
}

impl TryFrom<&u32> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: &u32) -> Result<Self, Self::Error> {
        (*sym).try_into()
    }
}

impl TryFrom<&NonZeroU32> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: &NonZeroU32) -> Result<Self, Self::Error> {
        sym.try_into()
    }
}

impl TryFrom<&u64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: &u64) -> Result<Self, Self::Error> {
        (*sym).try_into()
    }
}

impl TryFrom<&NonZeroU64> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: &NonZeroU64) -> Result<Self, Self::Error> {
        sym.get().try_into()
    }
}

impl TryFrom<&usize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: &usize) -> Result<Self, Self::Error> {
        (*sym).try_into()
    }
}

impl TryFrom<&NonZeroUsize> for Symbol {
    type Error = SymbolOverflowError;

    #[inline]
    fn try_from(sym: &NonZeroUsize) -> Result<Self, Self::Error> {
        sym.get().try_into()
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
        // This conversion relies on size_of::<usize>() >= size_of::<u32>(),
        // which is ensured with a const assertion.
        const _: () = [()][!(size_of::<usize>() >= size_of::<u32>()) as usize];

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
        // This conversion relies on size_of::<usize>() >= size_of::<u32>(),
        // which is ensured with a const assertion.
        const _: () = [()][!(size_of::<usize>() >= size_of::<u32>()) as usize];

        sym.id() as usize
    }
}

impl From<&Symbol> for i64 {
    #[inline]
    fn from(sym: &Symbol) -> Self {
        sym.id().into()
    }
}
