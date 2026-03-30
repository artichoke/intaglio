# Repository Guidelines

## Project Structure & Modules

- `src/` holds the library; key tables live in `bytes.rs`, `cstr.rs`,
  `osstr.rs`, and `path.rs`, with shared internals in `internal.rs` and exports
  in `lib.rs`.
- `tests/` contains integration tests; the `leak_drop/` suite exercises drop
  safety across symbol table types.
- Tooling configs: `Cargo.toml` for Rust deps, `deny.toml` for cargo-deny,
  `.config/spellcheck.toml` for spellchecking, `Rakefile` for dev tasks, and
  `package.json` for optional prettier tooling.

## Build, Test, and Development Commands

- `cargo build` – compile the crate with default features.
- `cargo test` – run the full test suite; append a filter (e.g.,
  `cargo test drop`) to target specific cases.
- `bundle exec rake fmt` – format Rust and text sources (rustfmt + prettier).
- `bundle exec rake lint` – run clippy and RuboCop; add `:clippy` or `:rubocop`
  to scope.
- `bundle exec rake test` – wrapper to run the Rust tests used in CI.
- `cargo doc --open` – build and open API docs locally.

## Coding Style & Naming

- Rust code is formatted with `rustfmt`; use 4-space indents, `snake_case` for
  functions/modules, `CamelCase` for types, and `SCREAMING_SNAKE_CASE` for
  consts.
- Avoid unsafe unless justified; keep `unsafe` blocks small and commented.
- Prefer `?` for error propagation and `Result<T, E>` returns over panics in
  library code.
- Keep public API docs (`///`) concise; add examples when behavior is subtle.

## Testing Guidelines

- Default to `cargo test`; integration tests live under `tests/`.
- Add focused tests near regressions; mirror naming like `*_drop` for
  drop-behavior cases.
- When changing internals, cover both borrowed and owned symbol paths and check
  token stability.
- Run tests with `MIRI_SYSROOT` in CI is handled; local Miri runs are optional
  but welcome.

## Commit & Pull Request Guidelines

- Commit messages follow imperative tone with a short summary (≈50 chars) and
  optional body explaining the why.
- For PRs: describe the change, note user-visible API impacts, link issues, and
  mention new tests. Include screenshots only if docs/UI artifacts change (rare
  here).
- Ensure `bundle exec rake fmt lint test` passes before requesting review; CI
  must be green.

## Security & Configuration Tips

- Keep toolchains in sync with `mise.toml` and Rust stable (see README);
  bump MSRV only with justification.
- Use `cargo deny check` before dependency updates; update the advisory DB with
  `cargo deny --all-features --locked check` if needed.
