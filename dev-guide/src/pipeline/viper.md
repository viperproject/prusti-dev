# Viper verification stage

- (With Prusti server only) Send VIR to the server.
- VIR is encoded into Viper.
- The Viper verifier is called and the results are obtained.
- (With Prusti server only) Send verification results back to the client.

## Prusti server

[Prusti server](https://github.com/viperproject/prusti-dev/pull/43) is an optional component of Prusti that can significantly reduce verification times by running a background process. The background process keeps an instance of JVM open, which is what Viper backends use to perform verification of Viper code. With the server enabled, a client only needs to send VIR to the server and receive the results once they are ready.

> - [`prusti-viper/src/verifier.rs` - `Verifier::verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/verifier.rs#L259-L281) - verification with the server.
> - [`prusti-viper/src/verifier.rs` - `Verifier::verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/verifier.rs#L281-L288) - verification without the server.

## Encoding VIR to Viper

As noted in [the previous section](prusti.md#encoding-mir-to-vir), VIR is an intermediate representation separate from Viper AST. In this step the encoding from one to the other is performed.

> - [`prusti-server/src/verifier_runner.rs` - `VerifierRunner::verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-server/src/verifier_runner.rs#L60) - call to `to_viper`.
> - [`prusti-common/src/vir/to_viper.rs`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-common/src/vir/to_viper.rs) - implementation of `ToViper` trait.
