# Fixed bugs

## BUG-001: Overlapping remainders for empty ranges

`AddressRange::non_overlapping_ranges` could return overlapping remainders when
`other` was empty. Fixed in [CL 8546718](https://chromium-review.googlesource.com/c/crosvm/crosvm/+/8546718).

## BUG-002: Intermediate overflow in aligned allocation

`AddressAllocator::internal_allocate_with_align` could overflow while computing
alignment or an inclusive endpoint. Fixed in [CL 8548175](https://chromium-review.googlesource.com/c/crosvm/crosvm/+/8548175).

## BUG-003: Unchecked arithmetic in reserved MMIO region calculation

`SystemAllocator::new` could underflow or overflow `u64` when computing the
reserved region and remaining `high_mmio` range. Fixed in [CL 8576268](https://chromium-review.googlesource.com/c/crosvm/crosvm/+/8576268).
