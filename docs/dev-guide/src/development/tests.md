# Tests

Tests for the Prusti project can be executed using the Python wrapper script:

```bash
./x.py test
```

The script sets up environment variables just like in the [build](build.md) phase, then runs `cargo test`.

Any additional arguments are added to the `cargo test` command line. For example:

```bash
$ ./x.py test --all --verbose
```

## Filtering tests

The [options available](https://doc.rust-lang.org/book/ch11-02-running-tests.html) when running `cargo test` still apply. For example, to only run tests which contain `mod` in their name:

```bash
$ ./x.py test mod
```

## Additional flags

Some tests require setting additional flags, for example, to ensure that the number of quantifier instantiations is below a certain bound. This can be achieved by adding at the top of the test file `// compile-flags:` followed by the [list of arguments](../config/flags.md) to Prusti. For example, the following comment would bound the number of unique triggers used to instantiate a quantifier to 20:

```rust
// compile-flags: -Psmt_unique_triggers_bound=20
```

## Debugging tests

See [the debugging section](../development/debug.md).

