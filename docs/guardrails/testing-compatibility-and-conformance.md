# Testing, Compatibility, and Conformance

Artichoke Rust code should treat behavior as a public contract. Tests are not
only a way to catch mistakes. They are the project memory for Ruby
compatibility, platform semantics, crate feature behavior, unsafe invariants,
and release promises.

This guardrail is grounded in active crates such as `rand_mt`, `intaglio`,
`sysdir`, and `known-folders`, plus historical crates such as `boba`,
`cactusref`, `raw-parts`, and `strudel`.

## Default Stance

- Every bug fix should add or update a regression test unless the existing test
  already fails for the bug.
- Every public example should either compile as a doctest or clearly state why
  it is not executable.
- Every compatibility claim should have a fixture, upstream spec, golden vector,
  platform test, or explicit manual verification note.
- Every feature flag and supported target should be exercised in CI.
- Tests should protect behavior, not implementation accidents.

The target is not maximal test count. The target is a suite that makes it hard
to accidentally change a documented contract.

## Test Layers

Use the smallest test layer that can prove the contract.

Unit tests are appropriate for:

- pure algorithms
- boundary conditions
- internal invariants
- error conversions
- panic and rollback behavior

Integration tests are appropriate for:

- public crate workflows
- feature combinations
- platform behavior
- compatibility fixtures
- API examples that need a real downstream crate boundary

Doctests are appropriate for:

- README snippets
- crate-level examples
- subtle public API usage
- target-gated examples
- compile-fail examples for intentional misuse

Fuzz tests are appropriate for:

- parsers
- encoders and decoders
- round trips
- byte-oriented APIs
- APIs that consume external or untrusted input

Miri and sanitizer-style checks are appropriate for:

- unsafe code
- pointer and lifetime invariants
- drop behavior
- leak behavior
- unwind rollback
- layout assumptions

## Compatibility Tests

Compatibility tests should name the external behavior they are preserving.

Good Artichoke patterns include:

- `rand_mt` carries Ruby reproducibility tests for MT19937 output.
- `boba` keeps an upstream Bubble Babble encoding spec and fuzz targets for
  encode, decode, and roundtrip.
- `intaglio` tests unwind rollback after hasher panics.
- `intaglio` tests leak and drop behavior under Miri.
- `known-folders` tests both minimum and latest supported `windows-sys`
  versions.
- `sysdir` tests Darwin-specific path behavior, including `NEXT_ROOT`.
- `strudel` compares a Rust port of Ruby's `st_table` behavior against Ruby
  benchmark and API expectations.

When importing an upstream fixture, preserve enough context to explain where it
came from and what version of upstream behavior it represents.

## Ruby Conformance

For Artichoke VM work, conformance means behavior matches the documented MRI
target, not that the implementation resembles MRI internally.

Use Ruby conformance tests for:

- parser behavior
- core and stdlib methods
- exception classes and messages when they are externally visible
- encoding behavior
- path and filesystem behavior
- numeric edge cases
- object identity and mutation semantics
- random number generator output when MRI compatibility requires it

A Ruby compatibility feature is not done until:

- the relevant upstream spec passes
- the implementation has direct tests for Artichoke-specific edge cases
- any known divergence is documented
- the spec is added to the enforced set when appropriate

Prefer adding a narrow spec for each fixed bug. A broad spec import is useful
only when CI can keep it enforced.

## Regression Tests

A regression test should fail before the fix and pass after the fix.

Good regression tests:

- use the public API when the bug is public
- include the smallest input that demonstrates the issue
- name the behavior being protected
- avoid sleeping, networking, clocks, randomness, and host-specific paths unless
  those are the behavior under test
- include comments only when the expected behavior is not obvious from the
  assertion

Do not add weak tests that only execute code. Assert the result, error, panic,
drop, allocation, output vector, or platform behavior that could regress.

## Feature Matrix

Feature flags are public API, so they need tests.

For active crates, CI should cover:

- default features
- all features
- no default features
- each major optional integration feature when interactions matter
- docs for feature-gated APIs

When a crate supports `no_std`, the `no_std` configuration must compile in CI.
If the crate uses `alloc`, document and test the distinction between `core`,
`alloc`, and `std`.

Do not add a feature flag without adding at least one test or doctest that
proves the public behavior it enables.

## Platform Matrix

Platform behavior should be tested on real target runners when the crate calls
real platform APIs.

For supported platforms:

- build the crate
- run unit and integration tests
- compile examples
- build docs when docs are target-specific
- test minimum dependency versions when platform bindings have a wide range

For unsupported platforms:

- prove the crate compiles off-target when that is the promise
- prove modules are absent or empty when that is the promise
- prove examples are gated correctly
- prove docs do not claim support that is not compiled

An off-target build is still a compatibility promise. Keep it intentional.

## Unsafe Verification

Unsafe code should have tests that target the unsafe invariant, not just the
safe API happy path.

Use:

- Miri for aliasing, lifetime, and provenance-sensitive code
- leak tests for ownership and drop paths
- panic-injection tests for rollback behavior
- compile-fail tests for lifetime and auto-trait invariants
- 32-bit target tests for pointer-width assumptions
- real OS tests for platform FFI
- fuzzing when unsafe code consumes bytes or parsed input

When a test exists because of unsafe code, say which invariant it protects in
the test name or nearby comment.

## Golden Fixtures

Golden fixtures are useful when the upstream output is the contract.

Use golden fixtures for:

- Ruby compatibility output
- encoded and decoded byte streams
- RNG sequences
- generated binding snapshots
- CLI output when the output format is public
- platform constants when upstream headers are the source of truth

Golden fixtures should be small, named, and traceable. Avoid fixtures so large
that reviewers stop reading diffs. When a fixture changes, the PR should explain
which upstream behavior changed and why the new fixture is correct.

## Compile-Fail Tests

Some contracts are negative:

- a value must not be `Send`
- a lifetime must not escape
- an API must not exist off-target
- a feature-gated item must not compile without the feature
- an unsafe API must require an explicit unsafe call

Use doctest `compile_fail` examples or a compile-test harness when the negative
contract is important. Prefer compile-fail coverage for unsafe abstractions and
target-gated APIs.

## Flaky Tests

Flaky tests are bugs in the project infrastructure.

When a test is flaky:

- identify whether the flake is timing, ordering, randomness, platform drift,
  resource exhaustion, or upstream service behavior
- narrow the assertion to the real contract
- replace sleeps with synchronization where possible
- seed randomness or record the failing seed
- quarantine only with an issue and a path back to enforcement

Do not silently delete a flaky test that was protecting a real contract.

## CI Expectations

CI should make local expectations public.

For active Rust crates, the normal CI shape should include:

- `cargo build --workspace`
- `cargo test --workspace`
- `cargo test --workspace --all-features`
- `cargo test --workspace --no-default-features`
- `cargo fmt --check`
- `cargo clippy --workspace --all-features --all-targets`
- rustdoc with warnings denied
- MSRV checks for the declared `rust-version`
- platform jobs for supported platform APIs
- Miri, fuzz, or benchmark jobs when the crate needs them

CI may promote warnings to errors for repository validation. Avoid exporting
that policy through broad crate attributes that affect downstream builds.

## Test Data and Maintenance

Test data should be maintainable.

- Keep fixtures close to the tests that consume them unless they are reused.
- Document upstream source and version for imported fixtures.
- Avoid generated fixture churn in behavior PRs.
- Keep slow tests marked or separated so they can run in scheduled CI.
- Keep automation runbooks when fixture refreshes require judgment.

Test maintenance is code maintenance. A test that no one can understand will
eventually stop protecting the project.

## Review Checklist

- Does the change add or update a regression test?
- Does the test fail without the fix?
- Is the test at the right layer?
- Are feature combinations covered?
- Are supported and unsupported platforms covered?
- Are README examples compiled as doctests where practical?
- Are compatibility fixtures traceable to upstream behavior?
- Does unsafe code have Miri, leak, panic, or compile-fail coverage?
- Does a dependency range change test both ends of the supported range?
- Does CI still prove the README and Cargo metadata claims?

## References

- [Cargo Book: cargo test](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
- [rustdoc book: documentation tests](https://doc.rust-lang.org/rustdoc/write-documentation/documentation-tests.html)
- [Cargo Book: Features](https://doc.rust-lang.org/cargo/reference/features.html)
- [Miri](https://github.com/rust-lang/miri)
- [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz)
