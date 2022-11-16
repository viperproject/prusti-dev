# Debugging

The `x.py` script can be used to run Prusti on an individual file:

```bash
$ ./x.py run --bin prusti-rustc path/to/the/file.rs
```

See the list of [flags](../config/flags.md) for way to configure Prusti. Of particular use when debugging are:

 - [`PRINT_DESUGARED_SPECS`](../config/flags.md#print_desugared_specs)
 - [`PRUSTI_DUMP_VIPER_PROGRAM`](../config/flags.md#dump_viper_program)
 - [`PRUSTI_LOG`](../config/flags.md#log)

## Debugging tests

A proposed way of fixing Prusti limitations is to add a regression test and then use the following command to get Prusti output:

```bash
./x.py build --all && \
RUST_BACKTRACE=1 PRUSTI_DUMP_VIPER_PROGRAM=true PRUSTI_DUMP_DEBUG_INFO=true \
./x.py ++verbose verify-test <path-to-the-test-file>
```

This command does the following:

1. Ensures that Prusti is compiled.
2. Runs the specified test taking into account the configuration flags specified in the test file.
3. Dumps the information that is most commonly needed for debugging Prusti into the `log` directory.

Tip: to see the expanded Prusti specification macros, add the following comment at the beginning of the test file:

```rust
// compile-flags: -Zunpretty=expanded
```

### Debugging performance problems

In case you are debugging a performance problem and suspect that it is caused by quantifiers, append `--analyze-quantifiers` to the command after the `<path-to-the-test-file>`. This will run Z3 in tracing mode and produce CSV files with various statistics in `log/smt` directory. In case you want to see all terms that were used to trigger a specific quantifier, you can produce the list of them with the following command:

```bash
PRUSTI_SMT_TRACE_QUANTIFIER_TRIGGERS=<quantifier-id> \
./x.py ++verbose run --release --bin smt-log-analyzer log/smt/<function>/trace1.log
```

You can find the list of quantifier ids and names in `log/smt/<function>/trace1.log.unique-triggers.csv`. Running the `smt-log-analyzer` will generate `log/smt/<function>/trace1.log.quantifier-<quantifier-id>-triggers.csv` file containing all triggers used to instantiate the quantifier.

