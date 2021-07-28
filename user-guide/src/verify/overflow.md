# Overflow checks

The overflow checks are enabled by default.

When the overflow checks are enabled, Prusti models integers as bounded values with a range that depends on the type of the integer. Values of `u32` types, for example, would be modeled to be between `0` and `2^32 - 1`.

When the overflow checks are disabled, Prusti models each integer type as an unbounded integer.

There are two ways to disable overflow checks in Prusti, depending on how you use the tool:

- If you use Prusti from the IDE, create a file named `Prusti.toml` containing `check_overflows=false` in the same folder of the program that you want to verify.
- If you run Prusti from the command line, place the `Prusti.toml` in the folder from which you run Prusti, or set the `PRUSTI_CHECK_OVERFLOWS=false` environment variable.
