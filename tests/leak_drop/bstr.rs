use bstr::{BStr, BString};
use intaglio::Symbol;
use intaglio::bstr::SymbolTable;

#[test]
fn dealloc_owned_data() {
    let mut table = SymbolTable::with_capacity(0);
    for sym in crate::vectors::byte_symbols() {
        let symbol = BString::from(sym);

        let sym_id = table.intern(symbol.clone()).unwrap();

        assert!(table.is_interned(BStr::new(&symbol)));
        assert!(table.contains(sym_id));
        assert_eq!(Some(BStr::new(&symbol)), table.get(sym_id));
        assert_eq!(sym_id, table.intern(symbol.clone()).unwrap());
        assert!(table.is_interned(BStr::new(&symbol)));
        assert!(table.contains(sym_id));
        assert_eq!(Some(BStr::new(&symbol)), table.get(sym_id));

        assert_eq!(table.get(Symbol::new(0)).unwrap().len(), 100);
    }
}
