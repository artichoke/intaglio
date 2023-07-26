use intaglio::bytes::SymbolTable;
use intaglio::Symbol;

#[test]
fn dealloc_owned_data() {
    let mut table = SymbolTable::with_capacity(0);
    for sym in crate::vectors::byte_symbols() {
        let symbol = sym;

        let sym_id = table.intern(symbol.clone()).unwrap();

        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_slice()), table.get(sym_id));
        assert_eq!(sym_id, table.intern(symbol.clone()).unwrap());
        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_slice()), table.get(sym_id));

        assert_eq!(table.get(Symbol::new(0)).unwrap().len(), 100);
    }
}
