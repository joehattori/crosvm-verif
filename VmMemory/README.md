# VmMemory verification

The default build imports every `*/Spec.lean` module here; each states its exact
contracts and preconditions. The root Makefile lists the extracted functions.
`MemoryMapping` is verified against the `mmap(2)` and `munmap(2)` contracts in
[Syscalls/Mmap.lean](../Syscalls/Mmap.lean).

## Reading the mapping specifications

`MappingProperties` in [MemoryMapping/Spec.lean](MemoryMapping/Spec.lean) is the
primary mathematical contract. A successful result has the requested length,
is not `MAP_FAILED`, has an end address that fits in `usize`, respects a
requested non-null fixed address, and satisfies the requested alignment.
With no fixed address, both absent alignment and explicit zero alignment give
page alignment. For example, a successful request for 8192 bytes aligned to
65536 returns length 8192 and an address divisible by 65536.

`try_mmap_populate_spec` proves this contract directly about the translated
function, using private lemmas for syscall results, alignment arithmetic, and
trimming. There is no `TryMmapOutcome` or equivalent whole-function execution
predicate. `MappingResultProperties` only lifts the success properties over
Rust's `Result`: its error case is `True`. The constructor wrappers use the
same contract, and `MemoryMappingBuilder.BuildOutcome` states the final
mapping properties without existential intermediate outcomes.

These are success-only contracts: they exclude Aeneas failure/panic under
their stated assumptions, but do not promise successful allocation or classify
all ordinary Rust errors. Error requirements are proved separately:
`try_mmap_populate_not_page_aligned_spec` verifies rejection of a misaligned
fixed address without assuming any syscall contract, and
`build_populate_invalid_spec` verifies rejection of anonymous population.
Exact error precedence and complete syscall traces are no longer public
postconditions.

`Some(null)` can enter the alignment-reservation path, so fixed-address
preservation deliberately excludes null. Alignment equal to the page size
uses the default mapping path; the contract still guarantees that alignment.

The syscall contracts describe return values and numeric address geometry,
not OS memory state. `MunmapSpec` permits any C return code: Aeneas `ok ret`
means normal return, not `ret = 0`. Successful cleanup, page-rounding effects,
memory permissions/contents, ownership, and leak freedom are not established.
Review these assumptions and mathematical properties independently of the
source; a checked proof does not establish that they capture every intended
API requirement. See also the root trust boundary.

Not verified:
- `GuestMemory::find_region`, `offset_from_base`, and `end_addr`: the pinned
  translator rejects `Iter::find` and method items passed as closures
  (higher-ranked signatures), and closures that return borrows into regions.
- `GuestMemory` constructors, guest-memory access, descriptor cloning,
  formatting, and serialization.

See the root README for [build and extraction](../README.md#build-and-extraction)
and the [trust boundary](../README.md#trust-boundary).
