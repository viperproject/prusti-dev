# Prusti processing stage

- The MIR of functions that should be checked is obtained.
- MIR is encoded into VIR - Prusti's intermediate representation.
- VIR is enriched with `fold`/`unfold` statements and other ghost code.
- VIR is simplified and optimized.

> - [`prusti/src/verifier.rs` - `verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti/src/verifier.rs#L15-L72) - function combining the steps in this stage.

## MIR and VIR

Prusti starts with Rust's [MIR (mid-level intermediate representation)](https://rustc-dev-guide.rust-lang.org/mir/index.html). The MIR is a [CFG](https://en.wikipedia.org/wiki/Control-flow_graph)-based representation that encodes Rust in a highly simplified (and therefore easier to programmatically process) manner.

The output of this stage is VIR (Viper intermediate representation). The VIR is similar to Viper AST, but it is CFG-based and contains some extra instructions to aid the generation of `fold`/`unfold` statements. The conversion of VIR to Viper AST is straight-forward by design.

> - [`prusti-common/src/vir/ast`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/ast) - definitions of most VIR data structures, e.g. expressions.
> - [`prusti-common/src/vir/cfg`](https://github.com/viperproject/prusti-dev/tree/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-common/src/vir/ast) - definitions of the CFG-specific parts of VIR, i.e. methods composed of a graph of basic blocks.

## Finding functions to check

In this step, functions to be checked are found by visiting the HIR with a visitor that looks for Prusti-defined attributes.

> - [`prusti-interface/src/environment/mod.rs` - `Environment::get_annotated_procedures`](https://github.com/viperproject/prusti-dev/blob/9ca9cd1b9bcfd9870691fa5a7a957a90987ba4af/prusti-interface/src/environment/mod.rs#L156-L161)

## Encoding MIR to VIR

In this step, Rust MIR is encoded to VIR. Pure functions are treated separately, since they may be used in specifications. The details of this encoding are complex, but a high-level overview can be found in the [Prusti publication, Appendix A](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=AstrauskasMuellerPoliSummers19.pdf#appendix.A).

> - [`prusti-viper/src/verifier.rs` - `Verifier::verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/verifier.rs#L237-L241) - initialisation of the encoding queue.
> - [`prusti-viper/src/encoder/encoder.rs` - `Encoder::process_encoding_queue`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/encoder/encoder.rs#L1653-L1682) - processing loop for the encoding queue.
> - [`prusti-viper/src/encoder/procedure_encoder.rs`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/encoder/procedure_encoder.rs) - module for encoding impure functions.

## VIR processing

At the end of procedure encoding, `fold`/`unfold` statements are added. The VIR may also be optimized, e.g. by removing empty branches in `if` chains.

> - [`prusti-viper/src/encoder/foldunfold/mod.rs`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/encoder/foldunfold/mod.rs) - `fold`/`unfold` logic.
> - [`prusti-viper/src/verifier.rs` - `Verifier::verify`](https://github.com/viperproject/prusti-dev/blob/143e673dc19b4c1363efade90ffee4f77641ec11/prusti-viper/src/verifier.rs#L246-L249) - optional optimization.
