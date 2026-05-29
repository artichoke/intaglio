# Performance, Allocation, and Memory Behavior

Performance work in Artichoke Rust code should be tied to a user-visible or
runtime-visible contract. Speed, allocation behavior, memory footprint, and drop
behavior matter, but they should not become folklore or speculative complexity.

This guardrail is grounded in active crates such as `intaglio` and `rand_mt`,
plus historical performance-sensitive work in `strudel`, `raw-parts`, and
`cactusref`.

## Default Stance

- Correctness and compatibility come first.
- Measure before adding complexity for performance.
- Keep benchmarks close to the behavior they protect.
- Document allocation and capacity behavior when callers can observe it.
- Prefer simple safe Rust unless measurements justify a sharper tool.
- Treat memory leaks, double frees, and panic-corrupted state as correctness
  bugs, not only performance bugs.

The goal is not maximum speed in every path. The goal is predictable behavior
for the paths the crate asks users to care about.

## Performance Contracts

Performance is a contract when the crate documents or implies:

- bounded allocation
- `no_std` or `alloc` behavior
- low-copy or zero-copy behavior
- deterministic output
- stable state size
- FFI compatibility
- drop behavior for large graphs or tables
- compatibility with an upstream runtime benchmark

If a PR changes one of these properties, it needs a test, benchmark, or explicit
release note.

## Benchmarks

Benchmarks should answer a concrete question.

Good benchmark questions:

- Did an interner lookup regress?
- Did table insertion allocate more often?
- Did a drop path become nonlinear?
- Did a Ruby compatibility path get slower than the upstream baseline?
- Did avoiding a copy matter for realistic input sizes?
- Did a platform wrapper add hidden allocation?

Poor benchmark questions:

- Is this new abstraction faster in isolation?
- Does this micro-optimization improve a synthetic loop?
- Can unsafe code beat safe code on one local machine?

Use Criterion or another stable harness when benchmark history matters. Keep
inputs realistic and named. Include edge cases, but do not let edge cases be the
only benchmark.

## Benchmark Hygiene

Benchmarks should be reviewable.

- Use stable fixtures.
- Use `black_box` where the optimizer would otherwise remove the work.
- Separate setup from measured work.
- Report throughput when input size matters.
- Compare against the current implementation when possible.
- Avoid benchmarking debug builds.
- Avoid host-specific file paths, clocks, network, and random inputs.
- Record command lines for nonstandard benchmarks.

Do not commit benchmark results as proof without explaining the environment and
why the numbers are meaningful.

## Allocation Behavior

Allocation behavior is often more important than raw instruction count.

Document and test when public APIs promise:

- no allocation
- one allocation
- capacity reuse
- fallible reservation
- exact capacity
- bounded state size
- ownership transfer without copying
- caller-controlled buffers

Use `try_reserve` or fallible constructors when callers may need to handle
allocation failure. Use `reserve` when panic-on-allocation-failure is acceptable
and documented by ordinary Rust collection semantics.

## Capacity and State

Capacity is observable when callers can ask for it, reuse it, or pay for it.

For capacity-sensitive APIs:

- document whether capacity is retained after clear or rollback
- test that rollback does not leak partially inserted state
- test that panic paths leave structures usable
- avoid exposing exact internal capacity unless it is part of the contract
- prefer approximate or qualitative docs when implementation freedom matters

`intaglio`'s rollback tests are a useful pattern: they prove that a panic during
hashing does not corrupt the table.

## Memory Footprint

Memory footprint should be explicit when it affects embedding.

`rand_mt` documents that each RNG uses approximately 2.5 kilobytes of state and
suggests boxing when embedding the RNG in other structs. This is the right level
of user-facing memory guidance.

Document memory footprint when:

- the type is large
- the type is commonly embedded in other types
- the crate is useful in constrained environments
- state size is inherited from an upstream algorithm
- allocation strategy affects FFI or runtime integration

Avoid freezing private layout to document memory usage unless layout is already
public API.

## Copies and Borrowing

Avoiding copies is useful only when it preserves a real contract.

Prefer:

- borrowed inputs when ownership is not needed
- `Cow` only when both borrowed and owned paths are common
- caller-provided buffers when allocation control matters
- explicit ownership transfer for FFI or raw-parts APIs

Avoid:

- unsafe lifetime extension to skip a measured-insignificant clone
- returning references into storage that can be invalidated by ordinary safe
  calls
- storing borrowed data when owned data would make the API sound and simple

When avoiding a copy requires unsafe code, the benchmark and the safety proof
both need to exist.

## Data Structures

Data structure choices should match the public workload.

For hash tables, interners, and graph-like structures:

- document expected big-O behavior when users care
- test insertion, lookup, deletion, and iteration edge cases
- benchmark realistic sizes
- test panic or callback behavior during mutation
- consider deterministic output when compatibility requires it
- do not expose internal storage order unless it is intentional

`strudel` exists because Ruby hash table behavior and performance mattered. That
kind of work should stay tied to upstream behavior, not just isolated Rust
microbenchmarks.

## Drop and Leak Behavior

Drop behavior is both performance and correctness.

Test drop paths when code manages:

- graphs
- cycles
- arenas
- interners
- FFI handles
- raw allocations
- rollback guards
- foreign runtime values

Use leak tests when ownership transfer is subtle. Use Miri when pointer or
lifetime invariants are involved. Use benchmarks when drop cost is part of the
crate's purpose, as in `cactusref`'s drop benchmarks.

## `no_std`, `alloc`, and Embedded Use

`no_std` claims are memory behavior claims.

For `no_std` crates:

- keep `std` behind an explicit feature or test-only gate
- test `no-default-features`
- document whether `alloc` is required
- avoid dependencies that accidentally reintroduce `std`
- keep examples honest about heap usage

Do not contort an API to claim `no_std`. Prefer an honest `std` crate over a
fragile compatibility story.

## FFI and Runtime Performance

FFI performance work must account for boundary costs.

When optimizing FFI or runtime integration:

- measure the full boundary, not only the Rust function
- include conversion costs for strings, paths, and buffers
- include allocation and deallocation costs
- account for callback overhead
- preserve upstream ABI and error semantics
- avoid batching or caching that changes observable behavior

A fast wrapper that changes platform or Ruby semantics is a bug.

## CI and Regression Detection

Most benchmarks should not block every PR unless they are stable enough to
signal real regressions. Use the right enforcement level.

Good CI patterns:

- run correctness tests on every PR
- run Miri or leak tests for unsafe memory behavior
- run benchmark smoke tests to keep harnesses compiling
- run full benchmarks on demand or scheduled jobs
- record baseline changes in performance PRs

Do not let a benchmark harness rot because it is too slow for every PR. Move it
to a scheduled or manual job and keep it visible.

## Performance PRs

A performance PR should explain:

- which workload is improved
- why that workload matters
- which benchmark or measurement was used
- what changed in allocation behavior
- what complexity or unsafe code was added
- what compatibility risk was considered
- whether release notes should mention the change

If the PR cannot name the workload, it probably should be a cleanup PR or not be
done.

## Review Checklist

- Is there a concrete workload or compatibility contract?
- Is the change measured?
- Are benchmark inputs realistic and reviewable?
- Does allocation behavior change?
- Does memory footprint change?
- Does the change affect `no_std`, `alloc`, or feature behavior?
- Does the change add unsafe code only for measured benefit?
- Are panic, rollback, and drop paths still tested?
- Does FFI or platform conversion cost matter?
- Do docs need to mention new performance or memory behavior?

## References

- [Rust Performance Book: Benchmarking](https://nnethercote.github.io/perf-book/benchmarking.html)
- [Cargo Book: cargo bench](https://doc.rust-lang.org/cargo/commands/cargo-bench.html)
- [Criterion.rs](https://bheisler.github.io/criterion.rs/book/)
- [std::hint::black_box](https://doc.rust-lang.org/std/hint/fn.black_box.html)
- [std::collections::TryReserveError](https://doc.rust-lang.org/std/collections/struct.TryReserveError.html)
