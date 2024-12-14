# SPDX-FileCopyrightText: Robin Krahl <robin.krahl@ireas.org>
# SPDX-License-Identifier: CC0-1.0

all: check lint test

.PHONY: check
check:
	cargo check --all-targets --no-default-features
	cargo check --all-targets
	cargo check --all-targets --all-features

.PHONY: lint
lint:
	cargo fmt --all --check
	cargo clippy --workspace --all-targets
	cargo doc --workspace --no-deps --all-features
	reuse lint

.PHONY: test
test:
	cargo test --workspace --all-features

.PHONY: ci
ci: export RUSTFLAGS=-D warnings
ci: export RUSTDOCFLAGS=-D warnings
ci: check lint
