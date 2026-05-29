# Working in Public and Publishing OSS Crates

Artichoke Rust repositories are public project infrastructure. Treat every
repository as something a downstream user may copy from, depend on, or audit
without asking first. The public surface is not only the Rust API. It includes
issues, pull requests, release notes, CI, README examples, docs.rs output,
crates.io metadata, licenses, and automation prompts.

These guardrails are written for Artichoke crates such as `rand_mt`, `intaglio`,
`sysdir`, and `known-folders`, and they also reflect lessons from older crates
such as `boba`, `raw-parts`, `strudel`, `qed`, and `cactusref`.

## Default Stance

- Work in public by default. Prefer issues, pull requests, and documented
  automation runbooks over private notes.
- Make narrow changes. A PR should have one intent: a bug fix, feature,
  dependency update, CI update, docs update, or release prep.
- Assume published crates are permanent. Do not publish exploratory APIs unless
  the crate clearly describes its maturity and limitations.
- Prefer boring project mechanics. Users should not need to learn a custom task
  runner to build, test, audit, or publish a crate.
- Let Codex prepare routine changes, but review the diff as authored code. The
  human maintainer owns issue selection, release decisions, CI interpretation,
  and the public contract.

## Repository Shape

Every public Rust crate repository should have:

- `Cargo.toml` with accurate `name`, `version`, `rust-version`, `edition`,
  `license`, `repository`, `documentation`, `homepage`, `description`,
  `keywords`, `categories`, `readme`, and `include`.
- A README that can stand alone on GitHub, crates.io, and docs.rs.
- License files matching the Cargo manifest.
- CI for build, test, formatting, linting, documentation, audit, and publish.
- `deny.toml` that restricts licenses and sources.
- A contribution guide that describes local setup, common commands, testing
  expectations, dependency updates, and the Codex maintenance workflow.
- Automation runbooks only when they encode repeatable maintenance decisions
  that should survive across runs.

README files should include:

- What the crate does in one sentence.
- A minimal dependency stanza.
- A small, compiling example.
- Feature flags and default features.
- Platform support and off-target behavior, if relevant.
- MSRV and when it can be bumped.
- License.
- Maturity or soundness caveats when applicable.

Do not rely on badges, repository topics, or crates.io metadata to carry meaning
that belongs in the README.

## Public Issue and PR Discipline

Open or reuse an issue before larger work unless the change is purely routine
maintenance. The issue should explain the user-visible problem or maintenance
goal. Avoid vague issues such as "clean up code" unless they list concrete
outcomes.

Pull requests should:

- Link the issue or maintenance runbook.
- Explain what changed and why.
- Call out public API, MSRV, platform, dependency, unsafe, and release impacts.
- Include tests or explicitly explain why existing coverage is sufficient.
- Keep generated or mechanical churn separate from handwritten changes.
- Wait for CI to finish before merge.

Avoid mixing release prep with unrelated implementation work. Release prep is
its own PR unless the repository runbook explicitly says otherwise.

## Cargo Metadata

Cargo metadata is a user-facing API. Keep it precise.

- `description` should describe the crate, not the parent Artichoke project.
- `keywords` and `categories` should match the real public use case.
- `repository`, `homepage`, and `documentation` must point to live public URLs.
- `include` should be explicit and small. Library crates usually include source,
  tests, README, licenses, examples when useful, and generated bindings only
  when those bindings are intentionally part of the crate.
- Do not package vendored upstream source unless redistributing it is
  intentional and its license is documented.
- Keep `html_root_url` synchronized with `Cargo.toml` during release prep.

Library crates should generally not commit `Cargo.lock` unless there is a
specific reason. CI should generate a lockfile when tools require locked audits.

## Versioning and MSRV

Use semver as the public compatibility language.

- Patch releases are for compatible bug fixes, docs fixes, CI-only publish
  fixes, and low-risk internal cleanup.
- Minor releases may add API, widen supported dependency ranges, change MSRV, or
  change documented platform coverage.
- Major releases are required for semver-incompatible API removals or behavior
  changes that downstream code cannot absorb safely.
- MSRV bumps are public compatibility changes. In Artichoke crates, they may be
  made in minor releases when the README says so.
- Keep MSRV tests in CI. A crate is not MSRV-compatible unless CI proves it.

Dependency ranges are also compatibility promises. Prefer the narrowest range
that expresses what CI actually tests. For target-specific dependencies, test
the minimum supported version and the latest supported version when the range is
wider than one exact version.

## Publishing

Publishing should be tag-driven and repeatable.

Before tagging:

- Check that `Cargo.toml` version, README dependency examples, and
  `html_root_url` agree.
- Run the repository's build, test, formatting, linting, docs, and audit
  commands.
- Run `cargo package --allow-dirty` during release prep when the repository
  runbook requests it, and inspect the package file list.
- Confirm `cargo publish --dry-run` or equivalent package validation succeeds
  when practical.
- Confirm CI is green on the exact commit to be tagged.

The publish workflow should:

- Trigger only on `vX.Y.Z` tags.
- Validate that the tag version matches `Cargo.toml`.
- Wait for the CI workflow on the tagged commit.
- Use crates.io trusted publishing through OIDC instead of long-lived
  `CARGO_REGISTRY_TOKEN` secrets.
- Request only the permissions it needs, normally `contents: read`,
  `actions: read`, and `id-token: write` for the publish job.
- Use `persist-credentials: false` on checkout.

Never republish from a dirty or reconstructed tree. Publish what was reviewed,
merged, and tagged.

## CI and Supply Chain

CI should be a public statement of what the crate supports.

- Pin GitHub Actions by commit SHA for active repositories.
- Keep top-level workflow permissions empty or read-only and grant write
  permissions only to jobs that need them.
- Run `cargo deny` for advisories, licenses, bans, and sources.
- Treat new advisories as triage events. It is acceptable for advisory-only
  checks to report without blocking surprise breakage, but the result must be
  reviewed.
- Run `zizmor` or equivalent workflow linting for GitHub Actions.
- Keep `dependabot` or equivalent dependency automation scoped to useful
  updates.
- Keep automation prompts in `docs/automations/` when the decision process is
  more important than the schedule.

Generated maintenance PRs must be reviewed like hand-authored PRs. Confirm the
change is necessary, scoped, and validated before merging.

## Documentation Is Part of the Release

docs.rs is the public API reader for Rust users. It must build cleanly.

- Use
  `RUSTDOCFLAGS="-D warnings -D rustdoc::broken_intra_doc_links --cfg docsrs"`
  in CI for active crates.
- Configure `package.metadata.docs.rs` to build the targets that match the crate
  story.
- Use `doc(cfg(...))` for optional features and platform-specific modules when
  possible.
- Include README snippets in doctests when the crate presents examples as
  copy-pasteable code.
- Use `compile_fail` examples for off-target or misuse examples.

Do not publish docs that overclaim platform support, soundness, cryptographic
suitability, dependency compatibility, or MSRV.

## Maturity and Limitations

If a crate is experimental, say so plainly. `cactusref` is a good model: it
describes the idea, lists limitations, and warns that the crate may be unsound.
That is better than allowing users to infer maturity from badges or a version
number.

Limitations that should be documented include:

- Unsafe API obligations.
- Known unsoundness risk.
- Off-target empty crates.
- Deterministic but non-cryptographic randomness.
- Raw platform path semantics.
- Dependency range compatibility policy.
- Vendored upstream source and license treatment.

## Release Prep Checklist

- `Cargo.toml` version is final.
- README dependency stanza uses the final version.
- `src/lib.rs` `html_root_url` uses the final version.
- Changelog or release notes, if present, describe user-visible changes.
- MSRV policy still matches README and CI.
- Feature docs match `Cargo.toml`.
- docs.rs target config matches supported platforms.
- `cargo package` file list is correct.
- Publish workflow uses trusted publishing and minimal permissions.
- CI is green on the exact tagged commit.

## References

- [OpenAI Harness Engineering](https://openai.com/index/harness-engineering/)
- [Cargo Book: Publishing on crates.io](https://doc.rust-lang.org/cargo/reference/publishing.html)
- [crates.io trusted publishing](https://crates.io/docs/trusted-publishing)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
