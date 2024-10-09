# Fail on early and on unset variables in non-shebang recipes
set shell := ["bash", "-euo", "pipefail", "-c"]
# Allow usage of bash methods to handle multiple arguments and work around quoting issues
set positional-arguments
set quiet

rust_version         := `sed -nr 's/channel = "(.*)"/\1/p' rust-toolchain.toml`
rust_nightly_version := `sed -nr 's/channel = "(.*)"/\1/p' rust-toolchain-nightly.toml`

rust-version:
    echo '{{rust_version}}'

rust-nightly-version:
    echo '{{rust_nightly_version}}'