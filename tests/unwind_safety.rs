#[cfg(feature = "cstr")]
use std::ffi::CStr;
use std::ffi::OsStr;
use std::hash::{BuildHasher, Hasher};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use intaglio::{Symbol, SymbolTable};

#[derive(Clone, Debug)]
struct PanicBuildHasher {
    builds: Arc<AtomicUsize>,
}

impl BuildHasher for PanicBuildHasher {
    type Hasher = PanicHasher;

    fn build_hasher(&self) -> Self::Hasher {
        let build = self.builds.fetch_add(1, Ordering::SeqCst) + 1;
        PanicHasher { build, hash: 0 }
    }
}

#[derive(Debug)]
struct PanicHasher {
    build: usize,
    hash: u64,
}

impl Hasher for PanicHasher {
    fn finish(&self) -> u64 {
        self.hash
    }

    fn write(&mut self, bytes: &[u8]) {
        if self.build == 1 {
            panic!("panic during first HashMap::insert hashing");
        }
        for byte in bytes {
            self.hash = self.hash.wrapping_mul(131).wrapping_add(u64::from(*byte));
        }
    }
}

fn panic_build_hasher() -> PanicBuildHasher {
    PanicBuildHasher {
        builds: Arc::new(AtomicUsize::new(0)),
    }
}

#[test]
fn str_symbol_table_rolls_back_after_hasher_panic() {
    let mut table = SymbolTable::with_hasher(panic_build_hasher());

    let result = catch_unwind(AssertUnwindSafe(|| table.intern("attacker")));

    assert!(result.is_err());
    assert_eq!(table.len(), 0);
    assert_eq!(table.check_interned("attacker"), None);

    let sym = table.intern("victim").unwrap();
    assert_eq!(sym, Symbol::new(0));
    assert_eq!(table.get(sym), Some("victim"));
    assert_eq!(table.check_interned("victim"), Some(sym));
}

#[cfg(feature = "bytes")]
#[test]
fn bytes_symbol_table_rolls_back_after_hasher_panic() {
    let mut table = intaglio::bytes::SymbolTable::with_hasher(panic_build_hasher());

    let result = catch_unwind(AssertUnwindSafe(|| table.intern(&b"attacker"[..])));

    assert!(result.is_err());
    assert_eq!(table.len(), 0);
    assert_eq!(table.check_interned(&b"attacker"[..]), None);

    let sym = table.intern(&b"victim"[..]).unwrap();
    assert_eq!(sym, Symbol::new(0));
    assert_eq!(table.get(sym), Some(&b"victim"[..]));
    assert_eq!(table.check_interned(&b"victim"[..]), Some(sym));
}

#[cfg(feature = "cstr")]
#[test]
fn cstr_symbol_table_rolls_back_after_hasher_panic() {
    let mut table = intaglio::cstr::SymbolTable::with_hasher(panic_build_hasher());

    let result = catch_unwind(AssertUnwindSafe(|| table.intern(c"attacker")));

    assert!(result.is_err());
    assert_eq!(table.len(), 0);
    assert_eq!(table.check_interned(c"attacker"), None);

    let sym = table.intern(c"victim").unwrap();
    assert_eq!(sym, Symbol::new(0));
    assert_eq!(table.get(sym), Some::<&CStr>(c"victim"));
    assert_eq!(table.check_interned(c"victim"), Some(sym));
}

#[cfg(feature = "osstr")]
#[test]
fn osstr_symbol_table_rolls_back_after_hasher_panic() {
    let mut table = intaglio::osstr::SymbolTable::with_hasher(panic_build_hasher());

    let result = catch_unwind(AssertUnwindSafe(|| table.intern(OsStr::new("attacker"))));

    assert!(result.is_err());
    assert_eq!(table.len(), 0);
    assert_eq!(table.check_interned(OsStr::new("attacker")), None);

    let sym = table.intern(OsStr::new("victim")).unwrap();
    assert_eq!(sym, Symbol::new(0));
    assert_eq!(table.get(sym), Some(OsStr::new("victim")));
    assert_eq!(table.check_interned(OsStr::new("victim")), Some(sym));
}

#[cfg(feature = "path")]
#[test]
fn path_symbol_table_rolls_back_after_hasher_panic() {
    let mut table = intaglio::path::SymbolTable::with_hasher(panic_build_hasher());

    let result = catch_unwind(AssertUnwindSafe(|| table.intern(Path::new("attacker"))));

    assert!(result.is_err());
    assert_eq!(table.len(), 0);
    assert_eq!(table.check_interned(Path::new("attacker")), None);

    let sym = table.intern(Path::new("victim")).unwrap();
    assert_eq!(sym, Symbol::new(0));
    assert_eq!(table.get(sym), Some(Path::new("victim")));
    assert_eq!(table.check_interned(Path::new("victim")), Some(sym));
}
