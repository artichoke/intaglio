#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![cfg(feature = "cstr")]

use core::iter;
use std::ffi::CString;

use intaglio::cstr::SymbolTable;

#[cfg(not(miri))]
const ITERATIONS: usize = 100_000;
#[cfg(miri)]
const ITERATIONS: usize = 25;

#[test]
fn dealloc_owned_data_bytes() {
    let mut table = SymbolTable::with_capacity(0);
    for (i, byte) in (b'\x01'..b'\xFF').cycle().enumerate().take(ITERATIONS) {
        let len = (i / 256) + 100;
        let symbol = iter::repeat(byte).take(len).collect::<Vec<_>>();
        let symbol = CString::new(symbol).unwrap();

        let sym_id = table.intern(symbol.clone()).unwrap();

        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_c_str()), table.get(sym_id));
        assert_eq!(sym_id, table.intern(symbol.clone()).unwrap());
        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_c_str()), table.get(sym_id));
    }
}
