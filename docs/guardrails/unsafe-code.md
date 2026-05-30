# Working with Unsafe Code

Unsafe Rust is allowed in Artichoke only when it buys something concrete:
binding to an operating system API, preserving an FFI ABI, expressing an
ownership primitive Rust cannot express safely, or avoiding copies where the
crate's purpose depends on that representation. Unsafe is never a shortcut for
making the borrow checker quiet.

The active Artichoke examples are `intaglio`, `sysdir`, and `known-folders`.
Historical examples include `raw-parts`, `strudel`, and `cactusref`.

## Default Rule

If a crate does not need unsafe code, forbid it:

```rust
#![forbid(unsafe_code)]
```

`rand_mt` and `boba` follow this rule. Keep it that way unless the crate's
purpose changes enough to justify a design review.

If a crate does need unsafe code, make that fact visible at the crate root:

```rust
#![warn(unsafe_op_in_unsafe_fn)]
#![warn(clippy::undocumented_unsafe_blocks)]
```

Unsafe operations inside `unsafe fn` still need explicit `unsafe` blocks. This
keeps the proof obligation attached to the operation, not hidden by the function
signature.

## Acceptable Uses

Unsafe code may be appropriate for:

- Raw FFI bindings to C or platform APIs.
- Safe wrappers around platform APIs that transfer ownership through raw
  pointers.
- Rebuilding standard-library ownership primitives with explicit public safety
  contracts.
- Internal pointer/lifetime representations that are fully encapsulated behind a
  safe API and verified by tests.
- Macros that produce compile-time values through unsafe constructors after
  proving their inputs.

Unsafe code is not appropriate for:

- Avoiding a clone without proving aliasing and lifetime invariants.
- Speeding up a path that is not measured or user-visible.
- Replacing straightforward safe Rust with pointer arithmetic.
- Making public safe APIs depend on caller behavior that is not checked or
  encoded in the type system.

## Required Documentation

Every public `unsafe fn`, unsafe trait, unsafe impl, and unsafe constructor must
have a `# Safety` section. The section must name the caller obligations in terms
that can be checked during review.

Every unsafe block needs a nearby comment explaining why that specific operation
is sound. Good comments name the relevant invariant:

- pointer origin
- non-nullness
- alignment
- allocation layout
- initialization
- aliasing
- lifetime
- ownership transfer
- drop order
- thread-safety
- FFI ABI
- platform API contract

Avoid comments such as "Safety: trusted" or "Safety: obvious". They do not carry
proof.

## Encapsulation

Unsafe code should be concentrated in small modules with safe APIs around them.

Good local patterns:

- `known-folders` uses a guard around the `SHGetKnownFolderPath` out pointer so
  `CoTaskMemFree` runs on every return path.
- `sysdir` exposes raw bindings only on Apple targets and compiles to an empty
  crate elsewhere.
- `intaglio` keeps static-lifetime tricks inside internal symbol-table storage
  and tests drop behavior under Miri.
- `raw-parts` exposes `into_vec` as `unsafe` instead of hiding it in `From`.
- `strudel` isolates C ABI functions and raw table conversions in FFI modules.

Do not let unsafe assumptions leak into ordinary callers. If a safe function can
cause undefined behavior when called with ordinary safe values, the API is
unsound.

## Proof Obligations

Before adding or changing unsafe code, write down the proof. Use this checklist.

Pointers:

- Where did each pointer come from?
- Can it be null?
- Is it aligned for the pointee type?
- Is it valid for reads, writes, or both?
- Is it valid for the requested length?
- Is the computed offset within one allocation?

Allocation and ownership:

- Which allocator allocated the memory?
- Which value owns deallocation?
- Is the deallocation layout exactly the allocation layout?
- Can the memory be freed twice?
- Can the memory leak on panic or early return?

Initialization:

- Are all read bytes initialized?
- Are `MaybeUninit` values converted only after initialization?
- Are partially initialized structures cleaned up correctly?

Aliasing and lifetimes:

- Can a mutable reference coexist with any shared reference?
- Does an internal `'static` reference escape the type that owns the backing
  allocation?
- Does moving a wrapper retag or invalidate references under Stacked Borrows?
- Are drop order assumptions enforced by fields, guards, or `Drop`?

Unwinding:

- What happens if hashing, allocation, comparison, callback execution, or a
  user-provided function panics?
- Is partially inserted state rolled back?
- Are FFI callbacks unwind-safe, or is unwinding across the boundary impossible?

Thread-safety:

- Are `Send` and `Sync` inherited correctly?
- If there is an unsafe impl, does it have the same bounds as the safe owner it
  models?
- Are compile-fail tests needed to prevent accidental auto-trait widening?

FFI:

- Is the ABI correct?
- Are `repr(C)` types used where layout is public?
- Are callbacks and function pointers nullable or non-null?
- Is string encoding documented?
- Does ownership of out pointers match upstream docs?
- Are platform APIs available on every target where they are linked?

## Verification

Unsafe code needs more than ordinary unit tests.

Use the strongest applicable checks:

- Miri with strict provenance, symbolic alignment checks, and randomized layout.
- Leak tests for ownership and drop behavior.
- Panic-injection tests for rollback behavior.
- Compile-fail doctests for lifetime and auto-trait invariants.
- 32-bit target tests for pointer-width-sensitive code.
- Platform CI on the real OS when unsafe code calls OS APIs.
- Fuzzing when unsafe code consumes parsed, decoded, or external input.
- Sanitizers when they are available and not known-broken for the scenario.

When a sanitizer is disabled because the toolchain is broken, keep the disabled
job visible with a link to the upstream issue. Do not silently delete the intent
to test.

## Safe Wrappers Around Platform APIs

Safe platform wrappers must absorb the platform's raw-pointer obligations.

For a function like `SHGetKnownFolderPath`, the wrapper is responsible for:

- passing valid input pointers
- initializing out pointers correctly
- freeing returned memory exactly once
- measuring returned strings safely
- checking length conversions
- converting encoding explicitly
- mapping expected error codes to the documented Rust return type

The safe wrapper should not expose raw pointers unless raw pointers are the
point of the crate.

## Public Unsafe APIs

A public unsafe API is a compatibility contract. It must be worth carrying.

For each public unsafe API, document:

- why the API cannot be safe
- what the caller must guarantee
- what the function guarantees on success
- what remains true on panic or error
- whether calling it twice is valid
- how it interacts with ownership and drop

If the API mirrors `std`, cite the corresponding `std` safety contract and list
any differences. `raw-parts` mirrors `Vec::from_raw_parts`; this is the right
level of explicitness.

## Experimental Unsafe Code

If a crate is not proven sound, say so in the README and crate docs. Do not ask
users to infer risk from a version number or from the existence of Miri tests.

`cactusref` is the model here: it explains that cycle detection requires unsafe
bookkeeping and that the crate may be unsound. That disclosure is part of the
crate's safety story.

## Review Checklist

- Can this be written in safe Rust without unacceptable API or performance cost?
- Is unsafe code isolated to the smallest practical scope?
- Do all public unsafe items have `# Safety` docs?
- Does every unsafe block name the invariant it relies on?
- Are lifetime, aliasing, drop, and allocation assumptions tested?
- Is panic or callback failure handled?
- Are `Send` and `Sync` correct?
- Is off-target compilation safe and explicit?
- Has Miri or the relevant platform CI run?
- Does the README disclose the risk if users must uphold safety invariants?

## References

- [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
- [Rust Edition Guide: unsafe operations in unsafe functions](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-op-in-unsafe-fn.html)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)
