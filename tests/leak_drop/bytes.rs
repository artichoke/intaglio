use core::iter;

use intaglio::bytes::SymbolTable;

#[test]
fn dealloc_owned_data() {
    let mut table = SymbolTable::with_capacity(0);
    for (i, byte) in (b'\0'..b'\xFF').cycle().enumerate().take(crate::ITERATIONS) {
        let len = (i / 256) + 100;
        let symbol = iter::repeat(byte).take(len).collect::<Vec<_>>();

        let sym_id = table.intern(symbol.clone()).unwrap();

        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_slice()), table.get(sym_id));
        assert_eq!(sym_id, table.intern(symbol.clone()).unwrap());
        assert!(table.is_interned(&symbol));
        assert!(table.contains(sym_id));
        assert_eq!(Some(symbol.as_slice()), table.get(sym_id));
    }
}
