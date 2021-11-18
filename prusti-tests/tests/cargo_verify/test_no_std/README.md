# `test_no_std`
The goal of this test crate is to make sure that the `prusti-contracts` crate does not accidentally import the Rust standard library, in order to stay compatible with `#![no_std]` targets. It achieves this as follows: in `src/main.rs` it defines the `lang_item`s for `eh_personality` and `panic_impl`. The same `lang_item`s are automatically imported by the Rust standard library. Thus, if the `prusti-contracts` crate would have a dependency on the Rust standard library, compilation of the `test_no_std` crate would fail due to an intentional collision, with the error message:

```
error[E0152]: found duplicate lang item `eh_personality`
  --> src/main.rs:16:1
   |
16 | pub extern fn rust_eh_personality() {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: the lang item is first defined in crate `panic_unwind` (which `std` depends on)
   = note: first definition in `panic_unwind` loaded from ~/.rustup/toolchains/nightly-2021-11-02-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/lib/libpanic_unwind-8e7e86a00adbd98f.rlib
   = note: second definition in the local crate (`test_no_std`)

error[E0152]: found duplicate lang item `panic_impl`
  --> src/main.rs:20:1
   |
20 | pub extern fn rust_begin_panic(_info: &core::panic::PanicInfo) -> ! {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: the lang item is first defined in crate `std` (which `prusti_contracts` depends on)
   = note: first definition in `std` loaded from ~/.rustup/toolchains/nightly-2021-11-02-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/lib/libstd-8adcca4f1427867b.rlib
   = note: second definition in the local crate (`test_no_std`)

For more information about this error, try `rustc --explain E0152`.
error: could not compile `test_no_std` due to 2 previous errors

```

or

```
error: linking with `cc` failed: exit status: 1
  |
  ...
  = note: /usr/lib/gcc/x86_64-linux-gnu/7/../../../x86_64-linux-gnu/Scrt1.o: In function `_start':
          (.text+0x12): undefined reference to `__libc_csu_fini'
          (.text+0x19): undefined reference to `__libc_csu_init'
          (.text+0x26): undefined reference to `__libc_start_main'
          /path/to/prusti-dev/target/tmp/cit/t2/foo/target/verify/debug/deps/test_no_std-697bad6dd5255399.test_no_std.cbd72a6a-cgu.1.rcgu.o: In function `main':
          /path/to/prusti-dev/target/tmp/cit/t2/foo/src/main.rs:29: undefined reference to `printf'
          collect2: error: ld returned 1 exit status
          
  = help: some `extern` functions couldn't be found; some native libraries may need to be installed or have their path specified
  = note: use the `-l` flag to specify native libraries to link
  = note: use the `cargo:rustc-link-lib` directive to specify the native libraries to link with Cargo (see https://doc.rust-lang.org/cargo/reference/build-scripts.html#cargorustc-link-libkindname)

error: could not compile `test_no_std` due to previous error

```

The above error messages can be reproduced by removing the `#![no_std]` crate attribute in `prusti-contracts` or by adding another dependency to `Cargo.toml` which in turn depends on the Rust standard library.

Note: this test project does not have any `output.stdout` or `output.stderr` files in it. This is because the command `cargo build --quiet` will output nothing and finish with a successful exit code.

# Alternatives
There may also be other ways to test the same outcome, such as cross-compiling to a target platform that does not support the Rust standard library, e.g. `thumbv6m-none-eabi`. For this approach, the target has to be added through rustup via the command `rustup target add thumbv6m-none-eabi` and then define the build target in `.cargo/config`:

```toml
[build]
target = "thumbv6m-none-eabi"
```

However, this approach was not chosen, in order not to complicate the testing framework too much with targets that are not intended to run the Prusti verifier on (this would also slow down the test suite more).