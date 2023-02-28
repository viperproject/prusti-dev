# Customizable counterexample

A counterexample for structs and enums can be formatted by annotating the type with `#[print_counterexample()]`. This is only avaible if the [`unsafe_core_proof`](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html#unsafe_core_proof) flag is set to `true`.

## Syntax structs

If a struct is annotated, the macro must have at least one argument and the first argument must be of type String and can contain an arbitrary number of curly brackets. The number of curly brackets must match the number of the remaining arguments. The remaining arguments must either be a field name, if the fields are named, or an index, if the fields are unnamed. A field can be used multiple times.

```rust,noplaypen,ignore
#[print_counterexample("Custom message: {}, {}", field_1, field_2) ]
struct X {
    field_1: i32,
    field_2: i32,
}
```

## Syntax enums

If an enum is annotated, the macro must not contain any arguments. Each variant can be annotated in the exact same way as previously described. Only annotating a variant without the enum itself will result in a compile time error.

```rust,noplaypen,ignore
#[print_counterexample()]
enum X {
    #[print_counterexample("Custom message: {}, {}", 0, 1)]
    Variant1(i32, i32),
    #[print_counterexample("Custom message")]
    Variant2,
}
```
