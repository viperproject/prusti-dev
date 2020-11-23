# Overflow checks

There are two ways to enable overflow checks in Prusti, depending on how you use the tool:

- If you use Prusti from the IDE, create a file named `Prusti.toml` containing `CHECK_OVERFLOWS=true` in the same folder of the program that you want to verify.
- If you run Prusti from the command line, place the `Prusti.toml` in the folder from which you run Prusti, or set the `CHECK_OVERFLOWS=true` environment variable.

By default, overflow checks are disabled and Prusti models each integer type as an unbounded integer. When overflow checks are enabled, instead, Prusti models integers as bounded values with a range that depends on the type of the integer. Values of `u32` types, for example, would be modeled to be between `0` and `2^32 - 1`.
