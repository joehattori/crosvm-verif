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

$(LLBC_DIR)/resources.llbc:
	mkdir -p $(LLBC_DIR)
	PATH="$(TOOLCHAIN_DIR)/bin:$$PATH" $(CHARON) cargo \
		--preset=aeneas \
		--dest-file $(LLBC_DIR)/resources.llbc \
		--start-from 'crate::address_range' \
		--start-from 'crate::address_allocator::AddressAllocator::new' \
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
