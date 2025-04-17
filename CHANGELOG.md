# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.14.2](https://github.com/moia-oss/tinytime.rs/compare/v0.14.1...v0.14.2) - 2025-04-17

### Added

- Optional bincode support ([#117](https://github.com/moia-oss/tinytime.rs/pull/117))

### Other

- Document why bincode unit tests exist ([#116](https://github.com/moia-oss/tinytime.rs/pull/116))
- Bump the cargo group across 1 directory with 3 updates ([#115](https://github.com/moia-oss/tinytime.rs/pull/115))
- Bump chrono from 0.4.39 to 0.4.40 in the cargo group ([#113](https://github.com/moia-oss/tinytime.rs/pull/113))
- update Rust to 1.85.0 and edition 2024 ([#111](https://github.com/moia-oss/tinytime.rs/pull/111))

## [0.14.1](https://github.com/moia-oss/tinytime.rs/compare/v0.14.0...v0.14.1) - 2025-02-21

### Added

- Serde utility methods (#109)

## [0.14.0](https://github.com/moia-oss/tinytime.rs/compare/v0.13.1...v0.14.0) - 2025-02-20

### Added

- [**breaking**] feature gate chrono (#105)
- [**breaking**] feature gate serde (#104)

### Fixed

- [**breaking**] fix serde support for non self-describing formats (#107)

### Other

- add cargo common metadata (#108)
- minimize rand features (#106)
- Remove unnecessary dependencies (#102)

## [0.13.1](https://github.com/moia-oss/tinytime.rs/compare/v0.13.0...v0.13.1) - 2025-02-02

### Added

- add `Rem` and `RemAssign` impls for `Duration` and `Time` (#99)

### Other

- update rand to 0.9.0 (#101)
- bump serde_json from 1.0.135 to 1.0.138 (#98, #100)
- bump thiserror from 2.0.10 to 2.0.11 (#96)

## [0.13.0](https://github.com/moia-oss/tinytime.rs/compare/v0.12.7...v0.13.0) - 2025-01-10

### Added

- specify msrv (#95)

### Other

- [**breaking**] restrict panics (#94)
- remove `lazy_static` (#93)
- update rust to 1.84.0 (#92)
- bump the cargo group with 2 updates (#91)
- bump serde from 1.0.216 to 1.0.217 in the cargo group (#90)
- bump the cargo group across 1 directory with 2 updates (#89)
- bump the cargo group with 3 updates (#87)
- bump thiserror from 2.0.3 to 2.0.4 in the cargo group (#85)

## [0.12.7](https://github.com/moia-oss/tinytime.rs/compare/v0.12.6...v0.12.7) - 2024-11-22

### Other

- use Time::MAX in TimeWindow::widest ([#83](https://github.com/moia-oss/tinytime.rs/pull/83))
- bump serde_json from 1.0.132 to 1.0.133 in the cargo group ([#84](https://github.com/moia-oss/tinytime.rs/pull/84))
- Remove myself from codeowners
- bump the cargo group with 2 updates ([#82](https://github.com/moia-oss/tinytime.rs/pull/82))
- bump thiserror from 1.0.66 to 2.0.0 in the cargo group ([#81](https://github.com/moia-oss/tinytime.rs/pull/81))
- bump the cargo group with 2 updates ([#80](https://github.com/moia-oss/tinytime.rs/pull/80))
- fix nightly ([#78](https://github.com/moia-oss/tinytime.rs/pull/78))
- bump the cargo group with 4 updates ([#79](https://github.com/moia-oss/tinytime.rs/pull/79))
- fix nightly ([#77](https://github.com/moia-oss/tinytime.rs/pull/77))
- bump serde_json from 1.0.128 to 1.0.129 in the cargo group ([#76](https://github.com/moia-oss/tinytime.rs/pull/76))
- fix nightly ([#74](https://github.com/moia-oss/tinytime.rs/pull/74))

## [0.12.6](https://github.com/moia-oss/tinytime.rs/compare/v0.12.5...v0.12.6) - 2024-10-11

### Fixed

- fix lint issue

### Other

- dependabot tweaks ([#73](https://github.com/moia-oss/tinytime.rs/pull/73))
- use grouped dependabot updates ([#72](https://github.com/moia-oss/tinytime.rs/pull/72))
- Bump derive_more from 0.99.18 to 1.0.0 ([#69](https://github.com/moia-oss/tinytime.rs/pull/69))
- set dependabot interval to weekly ([#70](https://github.com/moia-oss/tinytime.rs/pull/70))
- update to rust 1.81.0 ([#68](https://github.com/moia-oss/tinytime.rs/pull/68))
- add Cargo.lock to avoid discrepancies with local runs and CI runs
- just not make
