# VmMemory verification

See [GuestAddress/Spec.lean](GuestAddress/Spec.lean) for verified contracts and
preconditions, and the [build guide](../README.md#build-and-extraction) for
extraction and verification commands.

The trust boundary includes Rust compilation, Aeneas translation, and the
correspondence of its standard-library models to Rust. Formatting, serialization,
inherited trait defaults, and guest-memory access are outside the current scope.
