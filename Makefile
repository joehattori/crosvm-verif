AENEAS_BIN ?= $(CURDIR)/aeneas-bin/bin
CHARON ?= $(AENEAS_BIN)/charon
AENEAS ?= $(AENEAS_BIN)/aeneas
TOOLCHAIN_DIR := $(shell $(CHARON) toolchain-path 2>/dev/null)

LLBC_DIR := $(CURDIR)/llbc
RESOURCES_MANIFEST := $(CURDIR)/crosvm/resources/Cargo.toml
VM_MEMORY_MANIFEST := $(CURDIR)/crosvm/vm_memory/Cargo.toml

.PHONY: all extract extract-resources extract-vm-memory verify aeneas-bin

all: verify

aeneas-bin:
	nix build path:$(CURDIR)/aeneas#aeneas -o $(CURDIR)/aeneas-bin

# SliceIter::find is an unused override with an unsupported higher-ranked
# signature in the pinned translator. The mapped slice iterator uses next.
# Specialize functions instantiated with mutable references and extract Option's
# residual conversion, including the return path of a mutable Option borrow.
# The pinned Charon validates options before expanding the preset, so its
# remove-adt-clauses and lift-associated-types settings must also be explicit.
# Exclude the unused Residual trait and its impls to avoid a specialization bug
# in the pinned Charon. Try::branch and FromResidual functions remain available.
$(LLBC_DIR)/resources.llbc:
	mkdir -p $(LLBC_DIR)
	PATH="$(TOOLCHAIN_DIR)/bin:$$PATH" $(CHARON) cargo \
		--preset=aeneas \
		--monomorphize-mut=except-types \
		--remove-adt-clauses \
		--lift-associated-types '*' \
		--dest-file $(LLBC_DIR)/resources.llbc \
		--start-from 'crate::address_range' \
		--start-from 'crate::address_allocator::AddressAllocator::new' \
		--start-from 'crate::address_allocator::AddressAllocator::internal_allocate_from_slot' \
		--start-from 'crate::address_allocator::AddressAllocator::internal_allocate_with_align' \
		--start-from 'crate::address_allocator::AddressAllocator::reverse_allocate' \
		--start-from 'crate::address_allocator::AddressAllocator::allocate' \
		--start-from 'crate::address_allocator::AddressAllocator::allocate_at' \
		--start-from 'crate::address_allocator::AddressAllocator::insert_at' \
		--start-from 'crate::address_allocator::AddressAllocator::release' \
		--start-from 'crate::address_allocator::AddressAllocator::release_containing' \
		--start-from 'crate::address_allocator::AddressAllocator::address_from_pci_offset' \
		--start-from 'crate::address_allocator::AddressAllocatorSet::new' \
		--start-from 'crate::address_allocator::AddressAllocatorSet::allocate' \
		--start-from 'crate::address_allocator::AddressAllocatorSet::allocate_at' \
		--start-from 'crate::address_allocator::AddressAllocatorSet::get' \
		--start-from 'crate::address_allocator::AddressAllocatorSet::release' \
		--start-from 'crate::address_allocator::AddressAllocatorSet::address_from_pci_offset' \
		--start-from 'crate::system_allocator::SystemAllocator::new' \
		--start-from 'crate::system_allocator::SystemAllocator::get_anon_alloc' \
		--start-from 'crate::system_allocator::SystemAllocator::allocate_irq' \
		--start-from 'crate::system_allocator::SystemAllocator::release_irq' \
		--start-from 'crate::system_allocator::SystemAllocator::reserve_irq' \
		--start-from 'crate::system_allocator::SystemAllocator::allocate_gpe' \
		--start-from 'crate::system_allocator::SystemAllocator::get_pci_allocator_mut' \
		--start-from 'crate::system_allocator::SystemAllocator::pci_bus_empty' \
		--start-from 'crate::system_allocator::SystemAllocator::allocate_pci' \
		--start-from 'crate::system_allocator::SystemAllocator::reserve_pci' \
		--start-from 'crate::system_allocator::SystemAllocator::release_pci' \
		--start-from 'crate::system_allocator::SystemAllocator::allocate_mmio_internal' \
		--start-from 'crate::system_allocator::SystemAllocator::allocate_mmio' \
		--start-from 'crate::system_allocator::SystemAllocator::reserve_mmio' \
		--start-from 'crate::system_allocator::SystemAllocator::mmio_allocator_any' \
		--start-from 'crate::system_allocator::SystemAllocator::mmio_pools' \
		--include 'core::option::{impl core::ops::try_trait::FromResidual<_> for _}::from_residual' \
		--opaque 'base::sys::unix::system_info::pagesize' \
		--exclude 'core::ops::try_trait::Residual' \
		--exclude '{impl core::ops::try_trait::Residual}' \
		--exclude 'core::slice::iter::{impl core::iter::traits::iterator::Iterator for _}::find' \
		--exclude 'serde_core' \
		--exclude 'serde' \
		--exclude 'crate::address_range::{impl core::fmt::Display for _}' \
		--exclude 'crate::address_range::{impl core::fmt::Debug for _}' \
		--exclude 'crate::address_range::_::{impl serde_core::ser::Serialize for _}' \
		--exclude 'crate::address_range::_::{impl serde_core::de::Deserialize for _}' \
		-- --manifest-path $(RESOURCES_MANIFEST)

extract: extract-resources extract-vm-memory

extract-resources: $(LLBC_DIR)/resources.llbc
	mkdir -p $(CURDIR)/Resources
	# Iterator methods absent from the pinned backend are supplied by FunsExternal.
	$(AENEAS) \
		-backend lean \
		-split-files \
		-filter-trait-methods \
		-dest $(CURDIR)/Resources \
		$(LLBC_DIR)/resources.llbc

# Unlike the resources slice, do not specialize mutable references: this slice
# has no such calls, and that pass rejects wrap's trait objects.
$(LLBC_DIR)/vm_memory.llbc:
	mkdir -p $(LLBC_DIR)
	PATH="$(TOOLCHAIN_DIR)/bin:$$PATH" $(CHARON) cargo \
		--preset=aeneas \
		--remove-adt-clauses \
		--lift-associated-types '*' \
		--dest-file $(LLBC_DIR)/vm_memory.llbc \
		--start-from 'crate::guest_address' \
		--start-from 'crate::guest_memory::MemoryRegion::start' \
		--start-from 'crate::guest_memory::MemoryRegion::end' \
		--start-from 'crate::guest_memory::MemoryRegion::contains' \
		--start-from 'crate::guest_memory::MemoryRegion::contains_range' \
		--start-from 'crate::guest_memory::MemoryRegion::new_from_shm' \
		--start-from 'base::mmap::MemoryMappingBuilder::new' \
		--start-from 'base::mmap::MemoryMappingBuilder::from_file' \
		--start-from 'base::mmap::MemoryMappingBuilder::from_shared_memory' \
		--start-from 'base::mmap::MemoryMappingBuilder::offset' \
		--start-from 'base::mmap::MemoryMappingBuilder::build' \
		--include 'base::mmap::MemoryMappingBuilder' \
		--include 'base::mmap::_::new' \
		--include 'base::mmap::_::from_file' \
		--include 'base::mmap::_::from_shared_memory' \
		--include 'base::mmap::_::offset' \
		--include 'base::mmap::Protection' \
		--include 'base::descriptor::AsRawDescriptor' \
		--include 'base::descriptor::SafeDescriptor' \
		--include 'base::descriptor::{impl base::descriptor::AsRawDescriptor for _}::as_raw_descriptor' \
		--include 'base::shm::{impl base::descriptor::AsRawDescriptor for _}::as_raw_descriptor' \
		--include 'base::mmap::MemoryMapping' \
		--opaque 'base::mmap::{impl base::mmap::MappedRegion for _}::size' \
		--include 'base::sys::linux::mmap::_::build' \
		--include 'base::sys::linux::mmap::_::wrap' \
		--include 'base::mmap::_::read_write' \
		--include 'base::mmap::_::_::call_once' \
		--include 'core::option::_::unwrap_or_else' \
		--include 'core::result::_::branch' \
		--include 'base::sys::linux::mmap::MemoryMapping' \
		--include 'base::sys::linux::mmap::_::new_protection' \
		--include 'base::sys::linux::mmap::_::from_fd_offset_protection_populate' \
		--include 'base::sys::linux::mmap::_::try_mmap' \
		--include 'base::sys::linux::mmap::_::try_mmap_populate' \
		--include 'base::sys::linux::mmap::{impl core::convert::From<base::mmap::Protection> for i32}::from' \
		--exclude 'core::ops::try_trait::Residual' \
		--exclude '{impl core::ops::try_trait::Residual}' \
		--exclude 'serde_core' \
		--exclude 'serde' \
		--exclude 'crate::guest_address::{impl core::fmt::Display for _}' \
		--exclude 'crate::guest_address::{impl core::fmt::Debug for _}' \
		--exclude 'crate::guest_address::_::{impl serde_core::ser::Serialize for _}' \
		--exclude 'crate::guest_address::_::{impl serde_core::de::Deserialize for _}' \
		-- --locked --manifest-path $(VM_MEMORY_MANIFEST)

extract-vm-memory: $(LLBC_DIR)/vm_memory.llbc
	mkdir -p $(CURDIR)/VmMemory
	$(AENEAS) \
		-backend lean \
		-split-files \
		-filter-trait-methods \
		-dest $(CURDIR)/VmMemory \
		$(LLBC_DIR)/vm_memory.llbc

verify:
	lake build
