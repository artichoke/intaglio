#![deny(clippy::all)]
#![deny(clippy::pedantic)]

use core::iter;
use intaglio::SymbolTable;

#[cfg(not(miri))]
const ITERATIONS: usize = 100_000;
#[cfg(miri)]
const ITERATIONS: usize = 25;

#[test]
fn dealloc_owned_data_str() {
    let mut table = SymbolTable::with_capacity(0);
    for (i, ch) in ('\0'..'\x7F').cycle().enumerate().take(ITERATIONS) {
        let len = (i / 256) + 100;
        let symbol = iter::repeat(ch).take(len).collect::<String>();

        let sym_id = table.intern(symbol.clone()).unwrap();

        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_str()), table.get(sym_id));
        assert_eq!(sym_id, table.intern(symbol.clone()).unwrap());
        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_str()), table.get(sym_id));
    }
}
