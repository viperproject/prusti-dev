# Vir

Definition of the Viper/Verification Intermediate Representation.

The build script will use `vir-gen` to copy the definitions of `defs/` into `gen/`, expanding the macros. In particular:
* `copy_module!(<module_path>);` copies the module `<module_path>`, rooted at `defs/`, to the call site of the macro. It is useful to give the same implementation to multiple types, because the copied module can simulate polymorphism by using relative imports with `super` to reference types defined outside the `copy_module!` macro call.
* `#![derive_for_all(<E>)]` adds `#[derive(<E>)]` to all types defined in the current and sub- modules.
* `#![derive_for_all_structs(<E>)]` is like `derive_for_all`, but only for structs.
* `#[derive_helpers]` derives constructors of enum variants.
* `#[derive_visitors]` derives visitors.
* `derive_lower!` derives visitors converting from one VIR to another.

The transformations between VIR layers are:
* `high` --(type unifications)--> `typed` --(fold-unfold generation)--> `middle` --> `low`
* `polymorphic` --(monomorphization)--> `legacy`

