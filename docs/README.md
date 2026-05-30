# Documentation

This directory contains maintenance documentation for this crate.

Use the crate `README.md` and crate docs for user-facing API documentation. Use
`CONTRIBUTING.md` for local development setup and commands. Use this directory
for project policy, guardrails, supply-chain posture, and recurring maintenance
runbooks.

## Guardrails

[`guardrails/`](guardrails/README.md) contains durable review standards for
common classes of work:

- API stability, semver, MSRV, and release-impacting changes.
- Rust implementation quality, lints, docs, and maintainability.
- Testing, compatibility, conformance, and regression coverage.
- Unsafe code, FFI, platform-specific behavior, and memory behavior.
- Working in public and publishing OSS crates.

Start with [`guardrails/README.md`](guardrails/README.md), then read the
guardrail that matches the change.

## Supply Chain

[`dependencies.md`](dependencies.md) describes dependency policy, audit
expectations, update posture, and how to evaluate dependency changes.

Use it for dependency additions, version range changes, audit findings,
Dependabot updates, and CI changes that affect dependency verification.

## Automations

[`automations/`](automations/README.md) contains runbooks for recurring
maintenance.

Use these docs when performing scheduled or mechanical work such as dependency
sweeps or GitHub Actions runner updates.

## Updating Docs

Update docs in the same PR when a change alters public behavior, compatibility
claims, feature behavior, MSRV, dependency policy, release process, automation
behavior, or guardrail expectations.
