RUST_NIGHTLY_VERSION  := $(shell sed -nr 's/channel = "(.*)"/\1/p' rust-toolchain-nightly.toml)
GRCOV_VERSION         := 0.8.19

install-nightly:
	rustup toolchain install $(RUST_NIGHTLY_VERSION)

tools/grcov/$(GRCOV_VERSION)/grcov:
	mkdir -p tools/grcov/$(GRCOV_VERSION)/ && \
	cd tools/grcov/$(GRCOV_VERSION) && wget https://github.com/mozilla/grcov/releases/download/v$(GRCOV_VERSION)/$(GRCOV_RELEASE) && tar -xvf $(GRCOV_RELEASE)
	rm tools/grcov/$(GRCOV_VERSION)/grcov-*.tar.bz2
	rustup component add llvm-tools-preview

.PHONY: test
test:
	cargo test --workspace --all-targets --all-features
	cargo test --workspace --doc

lint:
	cargo +$(RUST_NIGHTLY_VERSION) fmt \
		-- \
		--check
	cargo clippy \
		--workspace \
		--tests \
		--benches
	cargo doc \
		--all \
		--no-deps \
		--document-private-items

fmt:
	cargo +$(RUST_NIGHTLY_VERSION) fmt

udeps:
	cargo +$(RUST_NIGHTLY_VERSION) udeps

.PHONY: clean
clean:
	rm -rf target

.PHONY: build
build:
	cargo build

.PHONY: build-release
build-release:
	cargo build --release

.PHONY: coverage-lcov
coverage-lcov: tools/grcov/$(GRCOV_VERSION)/grcov
	export RUSTFLAGS="-Zinstrument-coverage" && \
	export RUSTC_BOOTSTRAP=1 && \
	export LLVM_PROFILE_FILE="llvm-%p-%m.profraw" && \
	cargo build && \
	cargo test --workspace --lib --bins && \
	tools/grcov/$(GRCOV_VERSION)/grcov . \
		-s . \
		--binary-path ./target/debug/ \
		-t lcov \
		--branch \
		--ignore-not-existing \
		--keep-only=/src/**/*.rs \
		-o ./coverage.lcov

.PHONY: coverage-html
coverage-html: tools/grcov/$(GRCOV_VERSION)/grcov
	export RUSTFLAGS="-Zinstrument-coverage" && \
	export RUSTC_BOOTSTRAP=1 && \
	export LLVM_PROFILE_FILE="llvm-%p-%m.profraw" && \
	cargo build && \
	cargo test --workspace --lib --bins && \
	tools/grcov/$(GRCOV_VERSION)/grcov . \
		-s . \
		--binary-path ./target/debug/ \
		-t html \
		--branch \
		--ignore-not-existing \
		--keep-only=/src/**/*.rs \
		-o ./coverage && \
		open coverage/index.html
