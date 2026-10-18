AENEAS_BIN ?= $(CURDIR)/aeneas-bin/bin
CHARON ?= $(AENEAS_BIN)/charon
AENEAS ?= $(AENEAS_BIN)/aeneas
TOOLCHAIN_DIR := $(shell $(CHARON) toolchain-path 2>/dev/null)

LLBC_DIR := $(CURDIR)/llbc
RESOURCES_MANIFEST := $(CURDIR)/crosvm/resources/Cargo.toml

.PHONY: all extract verify aeneas-bin

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

extract: $(LLBC_DIR)/resources.llbc
	mkdir -p $(CURDIR)/Resources
	# Iterator methods absent from the pinned backend are supplied by FunsExternal.
	$(AENEAS) \
		-backend lean \
		-split-files \
		-filter-trait-methods \
		-dest $(CURDIR)/Resources \
		$(LLBC_DIR)/resources.llbc

verify:
	lake build
