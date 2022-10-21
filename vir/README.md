# Vir

Definition of the Verification Intermediate Representation.

The build script will use `vir-gen` to copy the definitions of `defs` into `vir_gen`, expanding the macros.

In particular:
* `copy_module!(<module_path>);` copies the module `module_path` to the curent location. It is useful to give the same implementation to multiple types, because the copied module can use relative imports to access type defined outside the `copy_module!` macro call.
* `#![derive_for_all(<E>)]` recursively traverses all the inner modules and adds `#[derive(<E>)]` to all types definitions.
* `#![derive_for_all_structs(<E>)]` is like `derive_for_all`, but only for structs.
