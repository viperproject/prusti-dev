# Printing Counterexamples

Prusti can print counterexamples for verification failures, i.e., values for variables that violate some assertion or pre-/postcondition.
This can be enabled by setting [`counterexample = true`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#counterexample) in the `Prusti.toml` file, or with the `PRUSTI_COUNTEREXAMPLES=true` environment variable.

For example:
```rust,noplaypen
fn test_assert(x: i32) {
    assert!(x >= 10);
}
```
This will result in an error like this one:
```plain
[Prusti: verification error] the asserted expression might not hold
assert_counterexample.rs(3, 4): counterexample for "x"
initial value: 9
final value: 9
```

Note 1: There are no guarantees on which value gets returned for the counterexample. The result will be an arbitrary value that fails the assertion (in this case any value in the range `i32::MIN..=9`).
Note 2: Verification will be slower with `counterexamples = true`.


# Customizable counterexamples

A counterexample for structs and enums can be formatted by annotating the type with `#[print_counterexample(..)]`. This is only available if the [`unsafe_core_proof`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#unsafe_core_proof) flag is set to `true`.

## Syntax structs

If a struct is annotated, the macro must have at least one argument and the first argument must be of type String and can contain an arbitrary number of curly brackets. The number of curly brackets must match the number of the remaining arguments. The remaining arguments must either be a field name, if the fields are named, or an index, if the fields are unnamed. A field can be used multiple times.

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[print_counterexample("Custom message: {}, {}", field_1, field_2) ]
struct X {
    field_1: i32,
    field_2: i32,
}
```

## Syntax enums

If an enum is annotated, the macro must not contain any arguments. Each variant can be annotated in the exact same way as previously described. Only annotating a variant without the enum itself will result in a compile time error.

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
#[print_counterexample()]
enum X {
    #[print_counterexample("Custom message: {}, {}", 0, 1)]
    Variant1(i32, i32),
    #[print_counterexample("Custom message")]
    Variant2,
}
```
