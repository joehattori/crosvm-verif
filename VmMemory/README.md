# VmMemory verification

The default build imports every `*/Spec.lean` module here; each states its exact
contracts and preconditions. The root Makefile lists the extracted functions.
`MemoryMapping` is verified against the `mmap(2)` and `munmap(2)` contracts in
[Syscalls/Mmap.lean](../Syscalls/Mmap.lean).

## Reading the mapping specifications

Start with `MappingProperties` in
[MemoryMapping/Spec.lean](MemoryMapping/Spec.lean). It states six properties of
a successful returned value: the requested length, exclusion of `MAP_FAILED`,
an end address that fits in `usize`, preservation of a requested non-null
address, default page alignment when both optional arguments are absent, and
positive requested alignment when no address is supplied. For example, a
successful request for 8192 bytes aligned to 65536, with no address supplied,
returns a logical length of 8192 and an address divisible by 65536.

`try_mmap_populate_success_spec` connects the translated function directly to
these properties under the same assumptions as the detailed theorem. It is
success-only: its error branch imposes no condition. The stronger
`try_mmap_populate_spec` remains the specification used by proof automation;
`TryMmapOutcome` retains error behavior, syscall arguments, and trim geometry.
Its stages separate address validation, alignment reservation, and the final
file/anonymous mapping. The previous monolithic predicate was already proved
equivalent to this modular formulation; the refactor uses that formulation
directly and removes the redundant conversion proofs.

These distinctions matter when reviewing intended behavior:

- Alignment equal to the page size is treated like zero alignment and does
  not require an extra reservation.
- `Some(null)` can enter the alignment-reservation path; the guarantee about
  preserving an explicitly supplied address therefore excludes null.
- A reservation can fail before file-offset validation. An oversized offset
  does not unconditionally imply `InvalidOffset`.
- The small success contract does not yet state default page alignment for
  an explicit `Some(0)` alignment. This is a limitation of that summary, not
  evidence that the implementation returns an unaligned address.

A proof that implementation satisfies specification does not establish that
the specification captures the intended API. Review these mathematical
properties separately from the source, and add further requirements as
theorems rather than changing them to follow the implementation. Equivalence
of two specifications establishes preservation, not correctness of their intent.

The syscall contracts describe return values and numeric address geometry,
not the OS memory state. In particular, `MunmapSpec` allows any C return code:
Aeneas `ok ret` means normal return, not `ret = 0`. Neither successful cleanup,
the effects of page rounding, memory permissions/contents, nor leak freedom
are established by these mapping contracts. See also the root trust boundary.

Not verified:
- `GuestMemory::find_region`, `offset_from_base`, and `end_addr`: the pinned
  translator rejects `Iter::find` and method items passed as closures
  (higher-ranked signatures), and closures that return borrows into regions.
- `GuestMemory` constructors, guest-memory access, descriptor cloning,
  formatting, and serialization.

See the root README for [build and extraction](../README.md#build-and-extraction)
and the [trust boundary](../README.md#trust-boundary).
