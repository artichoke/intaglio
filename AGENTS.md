# Agent Instructions

You are working in `artichoke/intaglio`, a Rust crate that provides symbol
interners for strings, bytes, C strings, OS strings, and paths.

Users rely on stable token and lookup behavior, feature-gated interner families,
panic rollback behavior, allocation behavior, MSRV, and the public crate API.
Treat those as compatibility surfaces.

## Operating Loop

1. Classify the change before editing.
2. Use the matching workflow section below to choose the guardrails and runbooks
   to consult.
3. Keep the diff narrow. Do not mix behavior, dependency posture, release
   metadata, formatting, and automation cleanup unless the task requires it.
4. Add or update focused tests for behavior changes, especially changes that can
   affect interning, lookup, rollback, or drop behavior.
5. Run checks that match the risk of the change; use
   [CONTRIBUTING.md](CONTRIBUTING.md) for local command expectations. If a
   relevant check is skipped, explain why in the PR.
6. Update README, crate docs, guardrails, or runbooks when public behavior,
   compatibility claims, feature behavior, MSRV, dependency policy, or release
   process changes.

## Interner Behavior And Compatibility

Use this workflow for changes to token allocation, lookup semantics, insertion,
rollback on panic, drop behavior, or feature-gated interner behavior.

Consult:

- [Testing and conformance](docs/guardrails/testing-compatibility-and-conformance.md),
  for regression coverage and feature-matrix expectations.
- [Performance, allocation, and memory behavior](docs/guardrails/performance-allocation-and-memory-behavior.md),
  for allocation and hot-path behavior.
- [API stability, semver, and MSRV](docs/guardrails/api-stability-semver-and-msrv.md),
  if behavior changes affect public expectations.

Preserve existing token and lookup semantics unless the task explicitly asks for
a breaking compatibility change.

## Public API, Features, MSRV, And Releases

Use this workflow for API shape, feature flags, docs.rs metadata, crate
metadata, MSRV, semver, publishing, changelog, and release-readiness changes.

Consult:

- [API stability, semver, and MSRV](docs/guardrails/api-stability-semver-and-msrv.md),
  for public contract and compatibility impact.
- [Working in public and publishing](docs/guardrails/working-in-public-and-publishing-oss-crates.md),
  for OSS release and communication expectations.

Call out compatibility impact in the PR. Keep release-prep changes separate from
unrelated implementation cleanup.

## Unsafe, Lifetimes, And Memory Safety

Use this workflow for unsafe internals, lifetime relationships, pointer or slice
handling, panic paths, and changes that affect drop or leak behavior.

Consult:

- [Unsafe code](docs/guardrails/unsafe-code.md), for safety documentation,
  containment, and review expectations.
- [Performance, allocation, and memory behavior](docs/guardrails/performance-allocation-and-memory-behavior.md),
  for allocation and memory-behavior expectations.
- [Testing and conformance](docs/guardrails/testing-compatibility-and-conformance.md),
  for Miri and targeted regression coverage.

Keep unsafe boundaries small and explain any new unsafe requirement in code and
in the PR.

## Implementation Quality

Use this workflow for refactors, lint posture, error handling, documentation
quality, crate attributes, and maintainability changes that do not intentionally
change behavior.

Consult:

- [High-quality Rust code](docs/guardrails/high-quality-rust-code.md), for lint,
  documentation, and maintainability expectations.
- [Testing and conformance](docs/guardrails/testing-compatibility-and-conformance.md),
  if the refactor touches behavior-sensitive paths.

Prefer mechanical refactors that preserve behavior and are easy to review.

## Dependencies, CI, And Automation

Use this workflow for dependency ranges, audits, Dependabot, GitHub Actions,
runner image updates, labels, and recurring maintenance.

Consult:

- [Dependency posture](docs/dependencies.md), for supply-chain expectations.
- [Dependency sweep automation](docs/automations/dependency-sweep.md), for
  dependency update procedure.
- [GitHub Actions runner images](docs/automations/github-actions-runner-images.md),
  for runner maintenance.
- [Working in public and publishing](docs/guardrails/working-in-public-and-publishing-oss-crates.md),
  if the change affects release or user-facing maintenance policy.

Keep mechanical dependency and automation updates separate from behavior
changes.

## Documentation-Only Changes

Use this workflow for README, crate docs, guardrails, runbooks, and PR/process
documentation.

Consult:

- [High-quality Rust code](docs/guardrails/high-quality-rust-code.md), for
  documentation quality expectations.
- [Working in public and publishing](docs/guardrails/working-in-public-and-publishing-oss-crates.md),
  for public-facing OSS communication.
- The guardrail for the topic being documented when docs describe API, unsafe
  code, compatibility, dependency, performance, or release behavior.

Docs-only PRs may skip Rust tests when the PR explains why. Still run the repo
formatter.

## Pull Requests

- State the change class and compatibility impact.
- Use labels from `.github/labels.yaml`; include at least one `A-*` label.
- For automation-generated work, use `C-automation` and the `codex` label.
- Do not add a Codex tag to the title or description.
