use std::ffi::OsString;

use intaglio::osstr::SymbolTable;

#[test]
fn dealloc_owned_data() {
    let mut table = SymbolTable::with_capacity(0);
    for sym in crate::vectors::symbols() {
        let symbol = OsString::from(sym);

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
