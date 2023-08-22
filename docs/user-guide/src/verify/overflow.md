# Overflow checks

Overflow checks are enabled by default.

When overflow checks are enabled, Prusti models integers as bounded values with a range that depends on the type of the integer. Values of `u32` types, for example, would be modeled to be between `0` and `2^32 - 1`.

When overflow checks are disabled, Prusti models signed integers as unbounded integers.

Overflow checks can be disabled by setting the [`check_overflows`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#check_overflows) flag to `false`. See [Providing Flags](https://viperproject.github.io/prusti-dev/dev-guide/config/providing.html) in the developer guide for details.

By default, unsigned integers are modeled as being non-negative (`0 <= i`), even with overflow checks disabled. They can also be modeled as unbounded integers by setting the [`encode_unsigned_num_constraint`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#encode_unsigned_num_constraint) flag to `false`.
