# Artichoke Rust Guardrails

These documents are operating guardrails for maintaining Artichoke Rust crates.
They are written to make project judgment explicit enough for humans and coding
agents to apply consistently.

Read the guardrails that match the change before editing code, tests,
documentation, automation, or release metadata.

## Guardrails

- [Working in Public and Publishing OSS Crates](working-in-public-and-publishing-oss-crates.md)
- [High Quality Rust Code](high-quality-rust-code.md)
- [Testing, Compatibility, and Conformance](testing-compatibility-and-conformance.md)
- [API Stability, SemVer, and MSRV](api-stability-semver-and-msrv.md)
- [Working with Unsafe Code](unsafe-code.md)
- [FFI, Bindings, and Foreign Runtime Integration](ffi-bindings-and-foreign-runtime-integration.md)
- [Platform Specific Code](platform-specific-code.md)
- [Performance, Allocation, and Memory Behavior](performance-allocation-and-memory-behavior.md)

## Repository Posture

This repository also has dependency and automation posture docs:

- [Dependency and Supply Chain Posture](../dependencies.md)
- [Dependency Sweep Automation](../automations/dependency-sweep.md)

Treat these docs as part of the same maintenance harness. If a change violates
one of these guardrails, update the guardrail in the same pull request or
explain the exception in the pull request body.
