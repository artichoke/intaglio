use criterion::{criterion_group, criterion_main};

#[cfg(feature = "bytes")]
mod bytestring {
    use criterion::{BatchSize, Criterion, Throughput};
    use intaglio::bytes::SymbolTable;

    pub fn bench_allocate(c: &mut Criterion) {
        let mut group = c.benchmark_group("SymbolTable constructors");
        group.bench_function("SymbolTable::new", |b| b.iter(SymbolTable::new));
        group.bench_function("SymbolTable::with_capacity(10)", |b| {
            b.iter(|| SymbolTable::with_capacity(10))
        });
        group.bench_function("SymbolTable::with_capacity(0)", |b| {
            b.iter(|| SymbolTable::with_capacity(0))
        });
    }

    pub fn bench_repeatedly_intern(c: &mut Criterion) {
        let mut group = c.benchmark_group("SymbolTable::intern single string");
        group.throughput(Throughput::Elements(10_000));

        let bytestring: &'static [u8] = b"acdefg123456";

        let strings = vec![bytestring.to_vec(); 10_000];
        group.bench_function("Owned with borrowed first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(bytestring).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });

        let strings = vec![bytestring.to_vec(); 10_000];
        group.bench_function("Owned with owned first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(bytestring.to_vec()).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });

        let strings = vec![bytestring; 10_000];
        group.bench_function("Static borrowed with borrowed first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(bytestring).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });

        let strings = vec![bytestring; 10_000];
        group.bench_function("Static borrowed with owned first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(bytestring.to_vec()).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });
    }
}

mod utf8string {
    use criterion::{BatchSize, Criterion, Throughput};
    use intaglio::SymbolTable;

    pub fn bench_allocate(c: &mut Criterion) {
        let mut group = c.benchmark_group("str::SymbolTable constructors");
        group.bench_function("SymbolTable::new", |b| b.iter(SymbolTable::new));
        group.bench_function("SymbolTable::with_capacity(10)", |b| {
            b.iter(|| SymbolTable::with_capacity(10))
        });
        group.bench_function("SymbolTable::with_capacity(0)", |b| {
            b.iter(|| SymbolTable::with_capacity(0))
        });
    }

    pub fn bench_repeatedly_intern(c: &mut Criterion) {
        let mut group = c.benchmark_group("str::SymbolTable::intern single string");
        group.throughput(Throughput::Elements(10_000));

        let utf8string: &'static str = "acdefg123456";

        let strings = vec![utf8string.to_string(); 10_000];
        group.bench_function("Owned with borrowed first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(utf8string).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });

        let strings = vec![utf8string.to_string(); 10_000];
        group.bench_function("Owned with owned first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(utf8string.to_string()).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });

        let strings = vec![utf8string; 10_000];
        group.bench_function("Static borrowed with borrowed first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(utf8string).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });

        let strings = vec![utf8string; 10_000];
        group.bench_function("Static borrowed with owned first", move |b| {
            b.iter_batched(
                || strings.clone(),
                |strings| {
                    let mut table = SymbolTable::with_capacity(1);
                    let sym = table.intern(utf8string.to_string()).unwrap();
                    for string in strings {
                        assert_eq!(sym, table.intern(string).unwrap());
                    }
                },
                BatchSize::SmallInput,
            )
        });
    }
}

#[cfg(feature = "bytes")]
criterion_group!(
    bytes,
    bytestring::bench_allocate,
    bytestring::bench_repeatedly_intern,
);
criterion_group!(
    utf8,
    utf8string::bench_allocate,
    utf8string::bench_repeatedly_intern,
);
#[cfg(feature = "bytes")]
criterion_main!(bytes, utf8);
#[cfg(not(feature = "bytes"))]
criterion_main!(utf8);
