# Reporting stage

- The Prusti client reports compilation and verification errors.

In this final stage, any errors and warnings that occurred during verification are reported to the user.

> - [`prusti-viper/src/verifier.rs` - `Verifier::verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/verifier.rs#L292-L317) - collection of errors from verification call.
> - [`prusti-viper/src/encoder/errors/prusti_error.rs` - `PrustiError::emit`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/encoder/errors/prusti_error.rs#L95) - emission of Prusti errors as messages and source file spans into the compiler environment.
