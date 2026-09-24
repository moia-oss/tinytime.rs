# Fail on early and on unset variables in non-shebang recipes
set shell := ["bash", "-euo", "pipefail", "-c"]
# Allow usage of bash methods to handle multiple arguments and work around quoting issues
set positional-arguments
set quiet

@default: fmt lint test

rust_nightly_version := `sed -nr 's/channel = "(.*)"/\1/p' rust-toolchain-nightly.toml`
msrv                 := `sed -nr 's/rust-version = "(.*)"/\1/p' Cargo.toml`

msrv:
    echo '{{msrv}}'

test:
	cargo test --workspace --all-targets --all-features
	cargo test --workspace --doc --all-features

lint:
    cargo '+{{rust_nightly_version}}' fmt -- --check
    cargo clippy \
        --workspace \
        --tests \
        --benches \
        --all-targets \
        --all-features \
        --quiet \
        -- -D warnings
    cargo doc --all --no-deps --document-private-items --all-features --quiet

fmt:
	cargo '+{{rust_nightly_version}}' fmt

verify-msrv:
    cargo msrv verify --all-features --ignore-lockfile
