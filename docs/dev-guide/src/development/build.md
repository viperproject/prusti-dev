# Building

Once the [development setup](setup.md) is complete, Prusti can be compiled. Using the Python wrapper script:

```bash
$ ./x.py build
```

The script will set the following environment variables if they are not already set, before running `cargo build`:

| Variable | Default value | Description |
| --- | --- | --- |
| `JAVA_HOME` | Detected based on OS. | Java JDK location. |
| `RUST_TEST_THREADS` | `1` | Limits the number of threads used for running tests. |
| `LD_LIBRARY_PATH` (and `DYLD_LIBRARY_PATH` on macOS) | Detected inside `JAVA_HOME` | Path containing `libjvm.so` (`libjvm.dylib` on macOS). |
| `VIPER_HOME` | `viper_tools/backends` | Path containing `silicon.jar`, `carbon.jar`, and various supporting Java libraries. |
| `Z3_EXE` | `(VIPER_HOME)/../z3/bin/z3` | Path to the `z3` solver executable. |

Any additional arguments are added to the `cargo build` command line. For example:

```bash
$ ./x.py build --all --verbose
```

## Verbose mode

To see which environment variables `./x.py` is setting, the `++verbose` flag can be passed on the command line before the `cargo` command:

```bash
./x.py ++verbose build
```
