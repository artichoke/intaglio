# Platform Specific Code

Platform specific Rust code is not second-class code. It is a public
compatibility statement about operating systems, targets, linkers, encodings,
error codes, filesystem semantics, and CI coverage.

This guardrail is grounded in the active `sysdir` and `known-folders` crates,
plus FFI-heavy historical work in `strudel`.

## Platform Support Must Be Explicit

Every platform-specific crate or module should document:

- supported operating systems
- supported Rust target triples when the distinction matters
- minimum OS or API version
- off-target behavior
- required system libraries or frameworks
- path, string, and encoding semantics
- whether the crate is raw bindings or a safe wrapper

`sysdir` states that it is empty on non-Apple platforms. `known-folders` states
that it is empty on non-Windows platforms. This is good. Empty off-target crates
are a valid design when they compile cleanly and the README says so.

Do not imply "cross-platform" when the real promise is "compiles off-target but
does nothing."

## Use `cfg` as an API Boundary

Keep platform gates simple and visible:

- Gate whole modules with `#[cfg(...)]`.
- Re-export platform modules only on supported targets.
- Prefer target-specific dependencies in `Cargo.toml`.
- Use `cfg_attr` in docs so examples compile only where they should.
- Add off-target examples or tests that prove unsupported targets fail in the
  documented way.

Avoid scattering target checks through business logic. A user should be able to
find the platform boundary quickly.

## Cargo and docs.rs

Cargo metadata should match the platform story.

- Use `categories` such as `os::windows-apis` or `os::macos-apis` only when the
  crate really targets those APIs.
- Put platform dependencies under target-specific dependency sections.
- Configure `package.metadata.docs.rs.targets` to build the targets users care
  about.
- Use `rustdoc-args = ["--cfg", "docsrs"]` when docs use `doc(cfg)`.
- Keep README examples and `html_root_url` current during release prep.

For platform crates, docs.rs is a compatibility artifact. If docs.rs builds only
one target, that target should be an intentional supported target.

## Preserve Platform Semantics

Do not clean up platform behavior unless the crate explicitly promises a
normalized abstraction.

`sysdir` correctly documents that Darwin search-path results:

- may contain a literal `~`
- may be prefixed by `NEXT_ROOT`
- may not be valid UTF-8

`known-folders` correctly converts Windows UTF-16 paths into `OsString` and then
`PathBuf`, while keeping the Win32 API boundary in one module.

Platform path code should avoid assuming:

- UTF-8
- `/` or `\` as universal separators
- normalized or absolute paths
- environment variable expansion
- case sensitivity
- stable folder presence across OS versions
- success for every documented folder ID

When exposing raw bindings, document that callers own normalization and
validation.

## Safe Wrappers and Raw Bindings

Choose one public story.

Safe wrapper crates should:

- expose Rust types such as `PathBuf`, `OsString`, `Option`, or `Result`
- manage raw pointer ownership internally
- map documented expected errors
- cite upstream API docs near the FFI call
- use guards for platform-owned allocations
- hide ABI details from safe callers

Raw binding crates should:

- expose C-compatible names and types intentionally
- preserve upstream constants and signatures
- avoid pretending raw pointers are safe
- include upstream headers or man pages when they are part of the source of
  truth
- document linker and OS availability

Do not mix the two stories accidentally. A crate can expose both raw bindings
and safe wrappers, but the boundary between them must be visible.

## CI Coverage

CI should prove the support matrix.

For target platforms:

- Build on real target runners.
- Run tests on real target runners.
- Build and run examples on real target runners.
- Test MSRV on a representative supported runner.
- Test dependency lower and upper bounds when a target-specific dependency range
  is intentionally wide.

For off-target platforms:

- Build the crate.
- Compile tests and examples when they are supposed to compile.
- Run tests that prove the crate is empty or returns the documented failure.
- Ensure docs still build or are gated correctly.

Prefer explicit runner labels when stable coverage matters. `ubuntu-latest`,
`windows-latest`, and `macos-latest` are useful only when the goal is to follow
GitHub's moving default. For MSRV, publish, docs, and platform-API coverage,
explicit labels are easier to audit.

## Dependency Ranges

Platform crates often depend on generated or externally versioned bindings.
Treat those ranges as public support promises.

For `windows-sys` style dependencies:

- Prefer widening an upper bound when source compatibility allows it.
- Test the oldest version in the range.
- Test the newest version in the range.
- Treat semver-incompatible binding upgrades as minor releases when the crate
  README documents that policy.
- Keep a maintenance runbook if the dependency needs repeated freshness checks.

Do not publish a range wider than CI proves.

## Generated and Vendored Bindings

Generated bindings are source code after they are checked in.

- Review generated diffs.
- Preserve local edits such as license headers and lint allowances.
- Do not combine binding refreshes with unrelated cleanup.
- Keep upstream source references and generation commands documented.
- Treat generated-content changes as release-relevant when users consume those
  bindings.

Vendored upstream sources need clear license treatment. `strudel` documents the
Ruby `st.c` and `st.h` sources and states that they are not distributed on
crates.io. That distinction matters.

## Linkage

Document what the crate links to and why.

- `sysdir` relies on `libSystem` and explicitly does not link to CoreFoundation,
  Foundation, or other frameworks.
- Windows APIs should list the relevant `windows-sys` feature groups.
- FFI crates should make C ABI entry points and exported symbols easy to audit.

Avoid adding build scripts for platform linkage unless they are necessary.

## Error Semantics

Platform APIs often expose many error reasons. Decide what the Rust API
promises.

- Use `Option` only when the crate intentionally treats all failures as absence.
- Use `Result` when callers need to distinguish permission, missing API, missing
  folder, invalid argument, unsupported OS, or buffer problems.
- Document expected error codes near the FFI call.
- Treat unknown error codes conservatively.

Changing error detail can be a semver-relevant API change.

## Review Checklist

- Does the README state supported platforms and off-target behavior?
- Are platform modules gated at the module boundary?
- Are target-specific dependencies scoped in `Cargo.toml`?
- Does docs.rs build the right targets?
- Do examples compile only where they should?
- Does CI run on real target OS runners?
- Are off-target builds tested?
- Are path and string encodings documented?
- Are upstream API versions and docs linked?
- Are generated bindings reviewed as source?
- Does dependency range policy match CI?
- Does the release need README, `html_root_url`, or docs.rs target updates?

## References

- [Cargo Book: Platform-specific dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#platform-specific-dependencies)
- [Rust Reference: Conditional compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)
- [docs.rs metadata](https://docs.rs/about/metadata)
