# Overflow checks

Overflow checks are enabled by default.

When overflow checks are enabled, Prusti models integers as bounded values with a range that depends on the type of the integer. Values of `u32` types, for example, would be modeled to be between `0` and `2^32 - 1`.

When overflow checks are disabled, Prusti models each integer type as an unbounded integer.

Overflow checks can be disabled by setting the [`check_overflows`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#check_overflows) flag to `false`. See [Providing Flags](https://viperproject.github.io/prusti-dev/dev-guide/config/providing.html) in the developer guide for details.
