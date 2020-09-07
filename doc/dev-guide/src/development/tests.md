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
