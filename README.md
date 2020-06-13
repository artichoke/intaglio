# intaglio

[![GitHub Actions](https://github.com/artichoke/intaglio/workflows/CI/badge.svg)](https://github.com/artichoke/intaglio/actions)
[![Discord](https://img.shields.io/discord/607683947496734760)](https://discord.gg/QCe2tp2)
[![Twitter](https://img.shields.io/twitter/follow/artichokeruby?label=Follow&style=social)](https://twitter.com/artichokeruby)
<br>
[![Crate](https://img.shields.io/crates/v/intaglio.svg)](https://crates.io/crates/intaglio)
[![API](https://docs.rs/intaglio/badge.svg)](https://docs.rs/intaglio)
[![API master](https://img.shields.io/badge/docs-master-blue.svg)](https://artichoke.github.io/intaglio/intaglio/)

UTF-8 and bytestring interner and symbol table. Used to implement storage for
the [Ruby `Symbol`][symbol] and the constant name table in [Artichoke
Ruby][artichoke].

> Symbol objects represent names and some strings inside the Ruby interpreter.
> They are generated using the `:name` and `:"string"` literals syntax, and by
> the various to_sym methods. The same `Symbol` object will be created for a
> given name or string for the duration of a program's execution, regardless of
> the context or meaning of that name.

Intaglio is a UTF-8 and bytestring interner, which means it stores a single copy
of an immutable `&str` or `&[u8]` that can be referred to by a stable `u32`
token.

Interned strings and bytestrings are cheap to compare and copy because they are
represented as a `u32` integer.

_Intaglio_ is an alternate name for an _engraved gem_, a gemstone that has been
carved with an image. The Intaglio crate is used to implement an immutable
Symbol store in Artichoke Ruby.

This crate depends on [`bstr`].

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
intaglio = "0.1"
```

Then intern bytestrings like:

```rust
fn intern_and_get() -> Result<(), Box<dyn std::error::Error>> {
    let mut table = intaglio::SymbolTable::new();
    let name: &'static [u8] = b"abc";
    let sym = table.intern(name)?;
    let retrieved = table.get(sym);
    assert_eq!(Some(name), retrieved);
    assert_eq!(sym, table.intern(b"abc".to_vec())?);
    Ok(())
}
```

Or intern UTF-8 strings like:

```rust
fn intern_and_get() -> Result<(), Box<dyn std::error::Error>> {
    let mut table = intaglio::str::SymbolTable::new();
    let name: &'static str = "abc";
    let sym = table.intern(name)?;
    let retrieved = table.get(sym);
    assert_eq!(Some(name), retrieved);
    assert_eq!(sym, table.intern("abc".to_string())?);
    Ok(())
}
```

## Implementation

Intaglio interns owned and borrowed strings with no additional copying by
leveraging `Cow` and `Box::leak`.

## License

`intaglio` is licensed under the [MIT License](LICENSE) (c) Ryan Lopopolo.

[symbol]: https://ruby-doc.org/core-2.6.3/Symbol.html
[artichoke]: https://github.com/artichoke/artichoke
[`bstr`]: https://crates.io/crates/bstr
