use core::iter;
use std::ffi::OsString;

use intaglio::osstr::SymbolTable;

#[test]
fn dealloc_owned_data() {
    let mut table = SymbolTable::with_capacity(0);
    for (i, ch) in ('\0'..'\x7F').cycle().enumerate().take(crate::ITERATIONS) {
        let len = (i / 256) + 100;
        let symbol = iter::repeat(ch).take(len).collect::<String>();
        let symbol = OsString::from(symbol);

        let sym_id = table.intern(symbol.clone()).unwrap();

        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_os_str()), table.get(sym_id));
        assert_eq!(sym_id, table.intern(symbol.clone()).unwrap());
        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_os_str()), table.get(sym_id));
    }
}
