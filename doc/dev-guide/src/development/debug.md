# Debugging

The `x.py` script can be used to run Prusti on an individual file:

```bash
$ ./x.py run --bin prusti-rustc path/to/the/file.rs
```

See the list of [flags](../config/flags.md) and [arguments](../config/arguments.md) for way to configure Prusti. Of particular use when debugging are:

 - [`-Z print_desugared_specs`](../config/arguments.md)
 - [`PRUSTI_DUMP_VIPER_PROGRAM`](../config/flags.md#dump_viper_program)
 - [`PRUSTI_LOG`](../config/flags.md#log)
