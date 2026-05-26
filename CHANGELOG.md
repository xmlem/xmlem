## Unreleased

## 0.4.1

-  Fix entities handling.

## 0.4.0 (yanked)

- [BREAKING] Update dependencies.

## 0.3.3

- Fix handling of `&` in comments ([#13]).

## 0.3.2

- Fix handling of `&` in comments ([#13]).

[#13]: https://github.com/xmlem/xmlem/issues/13

## 0.3.1

- Fix compilation when `quick-xml/encoding` is enabled ([#12]).

[#12]: https://github.com/xmlem/xmlem/issues/12

## 0.3.0

- [BREAKING] Revert `Element::name` to previous behavior of including prefix
  ([#6]).
- [BREAKING] Wrap returned errors in a new `ReadError` for reading functions
  ([#7]).
- [BREAKING] Update dependencies ([#7]).
- [BREAKING] Future-proof `display::Config` to allow adding new options in
  compatible versions.
- Improve pretty formatting and avoid ever-increasing document size in
  read/write loops ([#5], [#8]).
- Replace panics with errors when reading ([#9], [#10]).

[#5]: https://github.com/xmlem/xmlem/issues/5
[#6]: https://github.com/xmlem/xmlem/pull/6
[#7]: https://github.com/xmlem/xmlem/pull/7
[#8]: https://github.com/xmlem/xmlem/pull/8
[#9]: https://github.com/xmlem/xmlem/pull/9
[#10]: https://github.com/xmlem/xmlem/pull/10
