# API Stability, SemVer, and MSRV

Artichoke crates should make compatibility decisions deliberately. A crate's
public contract includes more than public Rust items. It includes feature flags,
trait impls, target support, error behavior, panic behavior, docs.rs output,
dependency ranges, and the minimum supported Rust version.

This guardrail is grounded in active crates such as `rand_mt`, `intaglio`,
`sysdir`, and `known-folders`, plus historical crates such as `boba`,
`raw-parts`, `qed`, `strudel`, and `cactusref`.

## Default Stance

- Treat published APIs as permanent until a major release removes or changes
  them.
- Make public APIs smaller than internal implementations.
- Assume feature flags are public API.
- Assume target support is public API.
- Assume MSRV is public API.
- Prefer compatibility-preserving additions over behavior-changing edits.
- Use deprecation before removal when the old API is not actively harmful.

The goal is not to avoid change. The goal is to make change legible to
downstream users.

## What Counts as Public API

Public API includes:

- public modules, types, traits, functions, constants, and macros
- public fields and enum variants
- trait impls, including auto traits when they are observable
- blanket impl behavior
- feature flag names and meanings
- default feature sets
- `no_std`, `alloc`, and `std` support
- supported target triples and off-target behavior
- error types and error detail
- documented panic behavior
- docs.rs target and feature presentation
- Cargo metadata such as `rust-version`, license, and dependency ranges

Do not rely only on Rust visibility to decide whether a change is breaking.
Downstream users also depend on behavior and build configuration.

## SemVer Classification

Patch releases are appropriate for:

- compatible bug fixes
- documentation fixes
- CI and publish workflow fixes
- internal cleanup with no public behavior change
- tightening tests around existing behavior
- compatible dependency patch updates

Minor releases are appropriate for:

- adding public API
- adding feature flags
- adding supported platforms
- widening dependency ranges
- changing MSRV when the README says MSRV may move in minor releases
- adding error detail without breaking existing matching
- improving behavior in a way downstream code can absorb safely

Major releases are required for:

- removing public API
- renaming public API
- changing function signatures
- changing trait bounds in a breaking direction
- removing or changing feature flag meaning
- removing target support
- changing documented panic or error behavior incompatibly
- changing `no_std`, `alloc`, or `std` promises incompatibly

Some behavior changes are judgment calls. When in doubt, write the release notes
as if explaining the change to a downstream maintainer. If the explanation says
"you may need to change your code," it is probably not a patch release.

## MSRV Policy

`rust-version` is a promise. Keep it in `Cargo.toml`, document it in the README,
and test it in CI.

An MSRV bump should:

- be intentional
- appear in release notes
- update README text when present
- update CI and local setup docs
- be classified according to the crate policy
- be justified by a concrete dependency, language feature, or maintenance need

For Artichoke crates, MSRV bumps may be minor releases when the README says so.
Do not make an MSRV bump in a patch release unless the previous release could
not actually build on the documented MSRV and the patch is correcting that bug.

## Cargo Metadata

Cargo metadata should match the compatibility story.

- Keep `edition` and `rust-version` synchronized with the code.
- Keep `include` small and intentional.
- Keep `documentation`, `homepage`, and `repository` live.
- Keep README dependency snippets synchronized with release versions.
- Keep `html_root_url` synchronized with published versions.
- Keep docs.rs target metadata aligned with supported platforms.

Metadata drift creates user confusion even when the Rust code is correct.

## Feature Flags

Feature flags are public configuration API.

Adding a feature is usually minor. Removing a feature, changing a feature's
meaning, or moving API between features is usually major.

Feature flags should:

- be named after user-visible capability
- avoid exposing dependency implementation details when possible
- document default behavior
- avoid surprising semantic changes
- compose with other features
- be covered by CI
- be shown in docs.rs with `doc(cfg)` when practical

Avoid feature flags that cause the same public function to mean materially
different things unless the crate's purpose requires it and the docs say so.

## Target Support

Supported targets are public API.

Adding a target is usually minor. Removing a target is usually major. Changing
off-target behavior may be breaking if downstream users rely on the crate
compiling or being empty off-target.

For platform-specific crates:

- document supported OSes and triples
- document off-target behavior
- gate modules at obvious `cfg` boundaries
- test real supported runners
- test off-target builds
- configure docs.rs to show the intended target story

Do not claim cross-platform support when the real promise is target-gated
compilation.

## Error and Panic Stability

Errors and panics are observable behavior.

Changing from `Option` to `Result` is breaking. Changing an error enum can be
breaking unless the enum is `#[non_exhaustive]` and downstream matching remains
compatible. Removing a panic can be compatible, but changing a panic into silent
wrong behavior is not.

Public error types should:

- expose only details the crate is willing to stabilize
- use `#[non_exhaustive]` when future cases are likely
- avoid leaking platform implementation details unintentionally
- document expected absence versus exceptional failure

Public panic behavior should:

- be rare in library APIs
- be documented when it is part of an indexing or assertion contract
- be tested when it protects an invariant

## Trait Impl Stability

Trait impls can be breaking in both directions.

Adding an impl is usually compatible, but it can break downstream code through
method resolution or coherence. Removing an impl is usually breaking. Changing
auto-trait behavior such as `Send`, `Sync`, `UnwindSafe`, or `RefUnwindSafe` can
be breaking and should be treated carefully.

For unsafe or ownership-sensitive types:

- document intentional auto-trait behavior
- add compile-fail tests for negative auto-trait promises when important
- avoid unsafe impls unless the proof is written down
- use `#[repr(transparent)]` or `#[repr(C)]` only when layout is part of the
  contract

## Type Evolution

Design public types so they can evolve.

Prefer:

- private fields with constructors and accessors
- `#[non_exhaustive]` for public enums likely to grow
- newtypes for values that are easy to mix up
- sealed traits when downstream implementation would freeze internals
- error types that can grow without breaking exhaustive matches

Avoid:

- public fields that expose internal representation
- public helper types that exist only to simplify implementation
- trait methods that require future implementations to preserve accidental
  behavior
- making allocation strategy or storage layout public unless that is the point
  of the crate

`raw-parts` is a good example of making a risky representation visible without
pretending conversion back into a `Vec` is safe.

## Dependency Ranges

Dependency ranges are compatibility promises.

When widening a dependency range:

- test the oldest supported version
- test the newest supported version
- document the policy when the range crosses semver-incompatible versions
- make the release at least minor if downstream compatibility changes

When tightening a dependency range:

- explain why older versions no longer work
- classify the change according to downstream impact
- update automation runbooks when present

For target-specific dependencies such as `windows-sys`, do not publish a range
wider than CI proves.

## Deprecation

Use deprecation when users need time to move.

Deprecation should:

- name the replacement
- explain why the old API is deprecated
- avoid breaking builds by default
- be followed by a major release before removal when removal is still desired

Do not deprecate as a substitute for making a decision. If an API remains useful
and supportable, keep it.

## Compatibility Tooling

Use tools to find obvious breakage, but do not outsource judgment.

Useful checks include:

- `cargo semver-checks` for Rust API compatibility
- `cargo test` for behavior compatibility
- doctests for examples and compile-fail contracts
- MSRV CI for `rust-version`
- platform CI for target support
- dependency lower-bound checks for published ranges

SemVer tools cannot fully understand behavior, feature meanings, platform
semantics, performance promises, or upstream Ruby compatibility. Review still
has to make those calls.

## Release Checklist

- Does the release classification match the public impact?
- Did public API change?
- Did feature flags change?
- Did target support or off-target behavior change?
- Did MSRV change?
- Did dependency ranges change?
- Did error or panic behavior change?
- Did docs.rs output change materially?
- Did README, `html_root_url`, and Cargo metadata stay synchronized?
- Do release notes explain migration work when users need it?

## References

- [Cargo Book: SemVer compatibility](https://doc.rust-lang.org/cargo/reference/semver.html)
- [Cargo Book: Manifest `rust-version`](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [cargo-semver-checks](https://docs.rs/cargo-semver-checks/latest/cargo_semver_checks/)
- [Cargo Book: Features](https://doc.rust-lang.org/cargo/reference/features.html)
