# Repository Map

This file is a map for agents working in this repository. It points to the
source-of-truth docs, configuration, and code landmarks; it should not duplicate
the policy held by those files.

## Start Here

- `README.md`: crate purpose, supported interned value types, and public
  examples.
- `CONTRIBUTING.md`: local development setup and command expectations.
- `Cargo.toml`: crate metadata, feature flags, MSRV, dependency ranges, and
  docs.rs metadata.
- `docs/guardrails/README.md`: index for Rust, OSS, unsafe, platform, testing,
  API, FFI, and performance guardrails.
- `docs/dependencies.md`: dependency and supply-chain posture.
- `docs/automations/README.md`: recurring maintenance map.
- `.github/labels.yaml`: PR label vocabulary for this repository.

## Change Map

- Public API, semver, features, MSRV, or publishing:
  `docs/guardrails/api-stability-semver-and-msrv.md`,
  `docs/guardrails/working-in-public-and-publishing-oss-crates.md`,
  `Cargo.toml`, `README.md`, and `src/lib.rs`.
- Rust implementation quality, lints, error handling, or docs:
  `docs/guardrails/high-quality-rust-code.md`, `CONTRIBUTING.md`, `src/lib.rs`,
  and `.github/workflows/ci.yaml`.
- Unsafe, lifetime, allocation, panic, or rollback behavior:
  `docs/guardrails/unsafe-code.md`,
  `docs/guardrails/performance-allocation-and-memory-behavior.md`,
  `src/internal.rs`, `src/rollback.rs`, and `.github/workflows/miri.yaml`.
- Tests, feature matrix, or compatibility coverage:
  `docs/guardrails/testing-compatibility-and-conformance.md`,
  `tests/leak_drop/`, `tests/unwind_safety.rs`, and `.github/workflows/ci.yaml`.
- Dependency, audit, or runner maintenance: `docs/dependencies.md`,
  `docs/automations/dependency-sweep.md`,
  `docs/automations/github-actions-runner-images.md`, `.github/dependabot.yml`,
  `.github/workflows/audit.yaml`, and `.github/workflows/repo-labels.yaml`.
- Markdown, YAML, JSON, or generated formatting changes: `package.json`,
  `.prettierrc.yaml`, and `pnpm-lock.yaml`.

## Code Map

- `src/lib.rs`: crate-level docs, feature gates, lint configuration, and public
  exports.
- `src/str.rs`, `src/bytes.rs`, `src/bstr.rs`, `src/cstr.rs`, `src/osstr.rs`,
  and `src/path.rs`: type-specific interner implementations.
- `src/internal.rs`: shared interner internals and the main unsafe boundary.
- `src/rollback.rs`: rollback helpers for partially completed insertions.
- `src/convert.rs` and `src/eq.rs`: conversion and equality support shared by
  the public interners.
- `tests/leak_drop/`: drop and leak behavior coverage by interned type.
- `tests/unwind_safety.rs`: panic and unwind-safety coverage.

## Pull Request Map

- Use labels from `.github/labels.yaml`; lopopolo-owned repositories require at
  least one `A-*` label.
- For automation-generated work, use `C-automation` and add the `codex` label.
  Keep `codex` as the last label definition in `.github/labels.yaml`.
- Do not add a Codex tag to PR titles or descriptions.
