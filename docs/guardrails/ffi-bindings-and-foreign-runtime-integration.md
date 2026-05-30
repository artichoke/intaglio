# FFI, Bindings, and Foreign Runtime Integration

FFI code is a compatibility boundary between Rust and another runtime, operating
system, ABI, allocator, or language. It needs stronger guardrails than ordinary
Rust because neither side can see the other side's invariants.

This guardrail is grounded in active platform crates such as `sysdir` and
`known-folders`, historical FFI-heavy work in `strudel`, and Artichoke VM work
that integrates Rust with Ruby and C APIs.

## Default Stance

- Decide whether the crate exposes raw bindings, safe wrappers, or both.
- Keep the raw boundary small and obvious.
- Preserve upstream ABI and semantics exactly at the binding layer.
- Convert into Rust types only at a documented wrapper boundary.
- Match allocation and deallocation APIs.
- Never unwind across an FFI boundary.
- Treat generated bindings as reviewed source code.

FFI is not only unsafe Rust. It is also build metadata, symbol names, linkers,
headers, encodings, callbacks, runtime initialization, and teardown.

## Boundary Model

Every FFI module should answer four questions:

- Who calls whom?
- Who owns each pointer, buffer, handle, and callback?
- Which allocator frees each allocation?
- Which runtime invariants must already be initialized?

Common boundary shapes:

- Rust calls a platform C API and exposes a safe Rust wrapper.
- Rust exposes C ABI symbols for a foreign runtime to call.
- Rust ports a foreign data structure but keeps ABI-compatible layout.
- Rust embeds a foreign runtime and must follow its initialization rules.
- Rust consumes generated bindings from upstream headers.

The boundary model should be visible in module names, docs, and tests.

## Raw Bindings

Raw binding modules should preserve upstream names and signatures.

Raw bindings should:

- use `unsafe extern` blocks
- use `repr(C)` for public layout types
- use `core::ffi` or `std::ffi` C types
- keep constants and type aliases close to upstream naming
- include upstream header, man page, or API links when possible
- avoid adding safe behavior at the raw layer
- be target-gated when the symbols do not exist everywhere

`sysdir` is a good model for keeping bindgen output isolated in a raw module and
documenting local edits.

## Safe Wrappers

Safe wrappers should absorb foreign obligations so safe callers cannot trigger
undefined behavior.

Safe wrappers should:

- validate inputs before calling foreign code
- initialize out pointers correctly
- free foreign allocations exactly once
- convert strings and paths explicitly
- map expected absence or error states deliberately
- hide ABI details from safe callers
- document any preserved platform oddities

`known-folders` is a good model: the wrapper calls a Windows API, guards the
returned pointer, converts UTF-16 to `OsString`, and exposes `PathBuf` rather
than raw allocation ownership.

## ABI and Symbols

ABI is public API.

For Rust functions exported to foreign code:

- use the correct `extern "C"` ABI or the documented platform ABI
- keep exported symbol names intentional
- namespace symbols when possible
- document whether the crate builds as `cdylib`, `staticlib`, or Rust library
- avoid exposing Rust layout or Rust panics through C ABI
- keep callback signatures exact

For Rust 2024 and later, unsafe attributes such as `no_mangle`, `export_name`,
and `link_section` should be treated as explicit safety obligations. The symbol
namespace and linker behavior are part of the proof.

## Layout

Layout assumptions must be tested or generated from upstream.

Use `repr(C)` when layout is shared with C. Use `repr(transparent)` only when a
single-field wrapper intentionally has the same ABI as its field. Avoid relying
on Rust field order, enum layout, niche optimization, or padding unless the
layout is documented and tested.

For ABI-compatible structs:

- test `size_of`
- test `align_of`
- test important field offsets
- test integer widths
- test pointer-width-sensitive types on 32-bit and 64-bit targets when relevant

`strudel`'s FFI-compatible `st_table` work is the kind of code that needs these
tests.

## Ownership and Allocation

Allocation ownership must cross the boundary in one direction at a time.

For every pointer crossing FFI, document:

- who allocated it
- whether it may be null
- whether it points to one value, an array, or a sentinel-terminated sequence
- whether the memory is mutable
- who frees it
- which function frees it
- whether the caller may retain it after the call returns

Never free memory with a different allocator than the one that allocated it.
Rust `Box`, `Vec`, and `String` memory must not be freed by C unless the API is
explicitly designed around Rust allocation and exposes the matching destructor.

## Strings, Paths, and Bytes

String conversion is part of the API contract.

Document and test:

- UTF-8 versus platform-native encoding
- UTF-16 and surrogate handling
- interior NUL behavior
- lossy versus lossless conversion
- byte paths on Unix
- `OsString` and `PathBuf` conversion boundaries
- null-terminated versus length-delimited buffers

Do not convert to `String` when the platform can return non-UTF-8 paths.
`sysdir` correctly preserves the possibility of non-UTF-8 Darwin paths.

## Error Handling

Foreign APIs often expose error state outside the return value.

Error handling should:

- capture `errno`, `GetLastError`, HRESULT, or platform status immediately when
  the API requires it
- distinguish expected absence from exceptional failure when callers need that
  distinction
- avoid collapsing all failures into `None` unless that is the documented API
- preserve unknown error codes conservatively
- document which upstream errors are expected

Changing error detail can be semver-relevant when downstream code observes it.

## Callbacks

Callbacks are FFI in both directions.

For callback APIs:

- document who owns callback data
- document whether callbacks may be null
- document reentrancy
- document mutation rules while iterating
- forbid unwinding across the callback boundary
- handle callback panics before returning to foreign code
- preserve upstream return-code semantics

If a callback can mutate the structure being iterated, tests should cover
insert, delete, stop, and error paths.

## Unwinding

Rust panics must not cross a non-unwinding FFI boundary.

For exported C ABI functions:

- keep panics impossible, or catch them before returning
- translate panic or internal failure into a documented error code
- ensure partially mutated state is rolled back or left valid
- test callback panic behavior when callbacks are allowed

For imported foreign functions:

- assume foreign exceptions cannot safely enter Rust unless the ABI and runtime
  explicitly support that behavior
- keep unwinding assumptions local and documented

## Runtime Integration

Foreign runtimes have global invariants that ordinary Rust APIs do not.

For Ruby and C runtime integration, document:

- initialization requirements
- shutdown requirements
- global state
- thread and lock requirements
- garbage collection ownership
- value lifetime and rooting rules
- encoding state
- allocator boundaries
- callback and reentrancy rules

Do not model a foreign runtime handle as an ordinary Rust value unless the type
enforces the runtime invariant.

## Generated Bindings

Generated bindings are source code after they are committed.

Generated binding updates should:

- document the generator and version
- document the exact command
- document the SDK or header source
- preserve local lint and license edits
- be reviewed as code
- be separated from unrelated cleanup
- include tests or diff notes for API changes

`sysdir`'s bindings freshness runbook is the right shape: it names the header,
the bindgen command, manual edits, and the expected PR contents.

## Vendored Foreign Source

Vendored foreign source should be intentional and traceable.

For vendored source:

- record upstream project, version, and license
- separate local patches from upstream code when possible
- avoid modifying vendored code in behavior PRs unless the PR is about the
  vendored code
- document whether vendored files are included in published crates
- keep compatibility tests that compare against upstream behavior

`strudel` documents its vendored Ruby `st.c` and `st.h` sources and the fact
that they are not distributed on crates.io. That distinction should remain
visible.

## Testing

FFI tests should prove both Rust behavior and foreign boundary behavior.

Use:

- real target OS runners for platform APIs
- layout tests for ABI-compatible structs
- smoke tests that call exported symbols from C or the foreign runtime
- Miri where it can model the unsafe code
- leak tests for ownership transfer
- panic-injection tests for rollback behavior
- upstream fixtures for behavior compatibility
- 32-bit jobs for width-sensitive ABI code

Do not rely only on Rust unit tests for a C ABI surface. The foreign caller's
view is part of the API.

## Review Checklist

- Is the boundary raw bindings, safe wrappers, or both?
- Is every FFI call target-gated correctly?
- Are ABI, symbol, and layout assumptions documented?
- Are pointer ownership and allocator rules clear?
- Are strings, paths, and bytes converted losslessly when required?
- Are errors captured and mapped deliberately?
- Can a panic or foreign exception cross the boundary?
- Are callbacks reentrancy and mutation rules tested?
- Are generated bindings reviewed as source?
- Are vendored sources traceable to upstream?
- Does CI exercise the real foreign boundary?

## References

- [Rustonomicon: FFI](https://doc.rust-lang.org/nomicon/ffi.html)
- [Rust Reference: external blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)
- [Rust Edition Guide: unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html)
- [Cargo Book: Build scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html)
- [bindgen user guide](https://rust-lang.github.io/rust-bindgen/)
