# High Quality Rust Code

High quality Artichoke Rust code is small in surface area, explicit about its
contracts, strict in CI, and boring to maintain. It should be clear which
behavior is public API, which behavior is an implementation detail, and which
behavior is inherited from Ruby, Rust, an operating system, or an upstream C
API.

This document is grounded in patterns across active Artichoke crates such as
`rand_mt`, `intaglio`, `sysdir`, and `known-folders`, plus historical crates
such as `boba`, `qed`, `raw-parts`, `strudel`, and `cactusref`.

## Design Principles

- Prefer small crates with a narrow purpose.
- Make the public API harder to misuse than the underlying primitive.
- Use `Result` or `Option` for expected failure. Avoid panics in library APIs
  unless the panic is part of an intentionally documented indexing or assertion
  contract.
- Keep unsafe code out of crates that do not need it.
- Prefer `no_std` when it is true and useful, but do not contort APIs to claim
  `no_std`.
- Preserve upstream semantics when implementing Ruby compatibility, platform
  bindings, or C-compatible APIs. Do not normalize behavior unless the API says
  it normalizes.
- Favor direct tool invocations over custom wrappers.

The goal is not maximal abstraction. The goal is code that makes its invariants
obvious and keeps compatibility promises verifiable.

## Crate Root Policy

Active Artichoke crates should have crate-level lints that make maintenance fail
loudly:

```rust
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused_qualifications)]
#![warn(variant_size_differences)]
```

Use `deny` sparingly for individual lints that encode a stable project
invariant. Keep broad Clippy groups at `warn` in crate attributes so toolchain
and lint-set drift does not unexpectedly make the crate unusable for downstream
builds. CI may still promote warnings to errors for repository validation.

If a crate should have no unsafe code, add:

```rust
#![forbid(unsafe_code)]
```

If a crate contains unsafe code, add:

```rust
#![warn(unsafe_op_in_unsafe_fn)]
#![warn(clippy::undocumented_unsafe_blocks)]
```

Every `allow` should be local or justified. Avoid broad `allow` blocks that make
future review harder.

## Public API Quality

Public APIs should be:

- Minimal: expose what downstream users need, not every helper the
  implementation has.
- Typed: prefer newtypes, enums, and named fields over positional tuples when
  values are easy to mix up.
- Documented: every public item has a useful doc comment.
- Example-backed: subtle APIs have doctests or README examples.
- Semver-aware: avoid public helper types that would be hard to change later.
- Feature-aware: optional modules and APIs are behind documented features.
- Target-aware: platform-specific APIs are compiled and documented only where
  they exist.

`raw-parts` is a good model for avoiding hidden risk: it gives names to the
components of a `Vec`, but it does not implement `From<RawParts<T>> for Vec<T>`
because rebuilding the `Vec` must remain visibly unsafe.

## Documentation Quality

The crate docs and README should tell the same story. In active crates, prefer
including the README in doctests when examples are intended to compile.

Docs should cover:

- Purpose.
- Quick installation.
- Minimal usage.
- Feature flags.
- Platform behavior.
- MSRV.
- License.
- Safety or maturity caveats.

Docs should not overclaim:

- Do not call deterministic RNG constructors "random entropy".
- Do not call raw platform paths normalized filesystem paths.
- Do not describe an empty off-target crate as cross-platform behavior.
- Do not hide experimental or potentially unsound status.

Use `#[cfg_attr(docsrs, doc(cfg(...)))]` for optional modules and platform
modules so docs.rs reflects feature and target gates.

## Error Handling and Panics

Library code should not panic for normal user input. Prefer:

- `Result<T, E>` when the caller needs a reason.
- `Option<T>` when the platform API or lookup is naturally absent and the crate
  intentionally collapses reasons.
- Dedicated error enums when the crate exposes a meaningful failure taxonomy.

Panics are acceptable for:

- Test code.
- Compile-time assertion macros.
- Documented indexing operations where the caller has already supplied an
  invalid symbol or key.
- Internal invariant failures that indicate a bug in the crate.

When a panic path protects an invariant, add tests that exercise surrounding
state. `intaglio`'s rollback tests are a strong pattern: they trigger a panic in
hashing and then prove the symbol table can continue to operate correctly.

## Tests

Tests should prove contracts, not just lines.

At minimum, active crates should run:

- `cargo build --workspace`
- `cargo test --workspace`
- `cargo test --workspace --all-features`
- `cargo test --workspace --no-default-features`
- `cargo fmt --check`
- `cargo clippy --workspace --all-features --all-targets`
- documentation builds with warnings denied

Add focused coverage when the crate has extra risk:

- MSRV jobs for the declared `rust-version`.
- 32-bit target jobs for pointer-width logic.
- Target OS jobs for platform crates.
- Miri jobs for unsafe code and drop/lifetime invariants.
- Fuzz jobs for parsers, encoders, and decoders.
- Reproducibility vectors for compatibility with Ruby or upstream specs.
- Compile-fail doctests for auto-trait, lifetime, or target-gate invariants.

Use tests to encode compatibility facts. `rand_mt` carries Ruby reproducibility
tests; `known-folders` tests minimum and latest `windows-sys` versions; `sysdir`
tests both target and non-target behavior; `boba` fuzzes encode, decode, and
roundtrip.

## CI Quality

CI is part of the code quality standard. It should be strict enough that a green
branch means something.

- Set `RUSTFLAGS=-D warnings` in build, test, and lint jobs.
- Build and test default, all-feature, and no-default-feature configurations
  when the crate has features.
- Run docs with rustdoc warnings denied.
- Keep formatting and text formatting checks separate from build tests.
- Use explicit runner labels when runner version matters.
- Keep workflow permissions minimal.
- Use `persist-credentials: false` for checkout.
- Run scheduled CI to catch runner and toolchain drift.

CI should not silently stop testing a contract because a platform moved, a
feature was added, or a dependency range widened.

## Dependency Quality

Dependencies should earn their place.

- Prefer no dependencies for small crates when the standard library or `core` is
  enough.
- Use `default-features = false` when a dependency does not need its defaults.
- Keep platform dependencies under target-specific dependency sections.
- Document semver-incompatible dependency policy in the README when relevant.
- Test the dependency range you advertise.
- Run `cargo deny` for advisories, licenses, bans, and sources.

For `no_std` crates, verify every dependency is compatible with the claimed
`no_std` mode and does not accidentally pull in `std`.

## Feature Flags

Feature flags are public API.

- Name features after the user-visible capability they enable.
- Document default features and non-default features.
- Avoid feature flags that change semantics in surprising ways.
- Test default, all-features, and no-default-features.
- Use docs.rs `doc(cfg)` to show feature gates.

Adding a feature is usually a minor release. Removing or changing the meaning of
a feature is usually a major release.

## Performance and Memory

Performance work should be tied to a contract:

- Compatibility with Ruby behavior.
- Bounded allocation.
- `no_std` support.
- FFI compatibility.
- Reduced copying.
- Proven drop or leak behavior.

Avoid clever code that only improves a benchmark no one runs. If performance is
important, add a benchmark or reproducibility test that explains what is being
protected.

For allocation-sensitive crates:

- Document capacity behavior.
- Prefer `try_reserve` variants when callers may need fallible allocation.
- Test drop paths, rollback paths, and panic paths.
- Be explicit about internal pointer, lifetime, and ownership invariants.

## Review Checklist

- Is the public API smaller or clearer than the implementation?
- Are all new public items documented?
- Do examples compile on the targets where they are shown?
- Does CI cover default, all-feature, and no-default-feature builds?
- Does the change affect MSRV, semver, docs.rs output, or platform support?
- Are new dependencies justified, minimal, and allowed by `deny.toml`?
- Are panics limited to documented contracts or internal bugs?
- Is unsafe code absent, or isolated and justified?
- Do tests cover the behavior that could regress?

## References

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Cargo Book: Manifest format](https://doc.rust-lang.org/cargo/reference/manifest.html)
- [Cargo Book: Features](https://doc.rust-lang.org/cargo/reference/features.html)
