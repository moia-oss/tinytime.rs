# Fail on early and on unset variables in non-shebang recipes
set shell := ["bash", "-euo", "pipefail", "-c"]
# Allow usage of bash methods to handle multiple arguments and work around quoting issues
set positional-arguments
set quiet

@default: fmt lint test

rust_version         := `sed -nr 's/channel = "(.*)"/\1/p' rust-toolchain.toml`
rust_nightly_version := `sed -nr 's/channel = "(.*)"/\1/p' rust-toolchain-nightly.toml`

rust-version:
    echo '{{rust_version}}'

rust-nightly-version:
    echo '{{rust_nightly_version}}'

test:
	cargo test --workspace --all-targets --all-features
	cargo test --workspace --doc

lint strict="":
    cargo '+{{rust_nightly_version}}' fmt -- --check
    cargo clippy \
        --workspace \
        --tests \
        --benches \
        --all-targets \
        --all-features \
        --quiet \
        -- {{ if strict != "" { "-D warnings" } else { "" } }}
    cargo doc --all --no-deps --document-private-items --all-features --quiet

fmt:
	cargo '+{{rust_nightly_version}}' fmt

udeps:
	cargo '+{{rust_nightly_version}}' udeps

install-nightly:
	rustup toolchain install '{{rust_nightly_version}}'