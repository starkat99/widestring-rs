# Changelog

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- Additional unchecked functions on `WideCString`.
- All types now implement `Default`.
- `WideString::shrink_to_fit`
- `WideString::into_boxed_wide_str` and `Box<WideStr>::into_wide_string`.
- `WideCString::into_boxed_wide_c_str` and `Box<WideCStr>::into_wide_c_string`.
- `From` and `Default` implementations for boxed `WideStr` and boxed `WideCStr`.

### Changed
- Renamed `WideCString::from_vec` to replace `WideCString::new`. To create empty string, use
  `WideCString::default()` now.
- `WideCString` now implements `Drop`, which sets the string to an empty string to prevent invalid
  unsafe code from working correctly when it should otherwise break. Also see `Drop` implementation
  of `CString`.
- Writing changelog manually.
- Upgraded winapi dev dependency.

## [0.2.2] - 2016-09-09 <a name="0.2.2"></a>
### Fixed
- Make `WideCString::into_raw` correctly forget the original self.

## [0.2.1] - 2016-08-12 <a name="0.2.1"></a>
### Added
- `into_raw`/`from_raw` on `WideCString`. Closes [#2].

## [0.2.0] - 2016-05-31 <a name="0.2.0"></a>
### Added
- `Default` trait to wide strings.
- Traits for conversion of strings to `Cow`.
### Changed
- Methods & traits to bring to parity with Rust 1.9 string APIs.

## 0.1.0 - 2016-02-06 <a name="0.1.0"></a>
### Added
- Initial release.

[#2]: https://github.com/starkat99/widestring-rs/issues/2

[Unreleased]: https://github.com/starkat99/widestring-rs/compare/v0.2.2...HEAD
[0.2.2]: https://github.com/starkat99/widestring-rs/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/starkat99/widestring-rs/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/starkat99/widestring-rs/compare/v0.1.0...v0.2.0
