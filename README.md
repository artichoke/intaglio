# intaglio

[![GitHub Actions](https://github.com/artichoke/intaglio/workflows/CI/badge.svg)](https://github.com/artichoke/intaglio/actions)
[![Discord](https://img.shields.io/discord/607683947496734760)](https://discord.gg/QCe2tp2)
[![Twitter](https://img.shields.io/twitter/follow/artichokeruby?label=Follow&style=social)](https://twitter.com/artichokeruby)
<br>
[![Crate](https://img.shields.io/crates/v/intaglio.svg)](https://crates.io/crates/intaglio)
[![API](https://docs.rs/intaglio/badge.svg)](https://docs.rs/intaglio)
[![API trunk](https://img.shields.io/badge/docs-trunk-blue.svg)](https://artichoke.github.io/intaglio/intaglio/)

UTF-8 string and byte string interner and symbol table. Used to implement
storage for the [Ruby `Symbol`][symbol] table and the constant name table in
[Artichoke Ruby][artichoke].

> Symbol objects represent names and some strings inside the Ruby interpreter.
> They are generated using the `:name` and `:"string"` literals syntax, and by
> the various `to_sym` methods. The same `Symbol` object will be created for a
> given name or string for the duration of a program's execution, regardless of
> the context or meaning of that name.

Intaglio is a UTF-8 and byte string interner, which means it stores a single
copy of an immutable `&str` or `&[u8]` that can be referred to by a stable `u32`
token.

Interned strings and byte strings are cheap to compare and copy because they are
represented as a `u32` integer.

_Intaglio_ is an alternate name for an _engraved gem_, a gemstone that has been
carved with an image. The Intaglio crate is used to implement an immutable
Symbol store in Artichoke Ruby.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
intaglio = "1.4"
```

Then intern UTF-8 strings like:

```rust
fn intern_and_get() -> Result<(), Box<dyn std::error::Error>> {
    let mut table = intaglio::SymbolTable::new();
    let name: &'static str = "abc";
    let sym = table.intern(name)?;
    let retrieved = table.get(sym);
    assert_eq!(Some(name), retrieved);
    assert_eq!(sym, table.intern("abc".to_string())?);
    Ok(())
}
```

Or intern byte strings like:

```rust
fn intern_and_get() -> Result<(), Box<dyn std::error::Error>> {
    let mut table = intaglio::bytes::SymbolTable::new();
    let name: &'static [u8] = b"abc";
    let sym = table.intern(name)?;
    let retrieved = table.get(sym);
    assert_eq!(Some(name), retrieved);
    assert_eq!(sym, table.intern(b"abc".to_vec())?);
    Ok(())
}
```

## Implementation

Intaglio interns owned and borrowed strings with no additional copying by
leveraging `Cow` and a bit of unsafe code. CI runs `drop` tests under Miri and
LeakSanitizer.

## Crate features

All features are enabled by default.

- **bytes** - Enables an additional symbol table implementation for interning
  byte strings (`Vec<u8>` and `&'static [u8]`).

### Minimum Supported Rust Version

This crate requires at least Rust 1.56.0. This version can be bumped in minor
releases.

## License

`intaglio` is licensed under the [MIT License](LICENSE) (c) Ryan Lopopolo.

[symbol]: https://ruby-doc.org/core-2.6.3/Symbol.html
[artichoke]: https://github.com/artichoke/artichoke
