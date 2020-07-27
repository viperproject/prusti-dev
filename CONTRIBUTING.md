# Contributing

## Getting Started

At the repository root, we provide a Python3 script `x.py` that sets up the necessary configuration flags and calls `cargo` with the provided arguments.

To install the necessary dependencies, run the following command:

```bash
./x.py setup
```

After the setup is complete, you can use `x.py` in the same way as you would use cargo. For example, you can compile the project and run all tests as follows:

```bash
./x.py build    # Compile Prusti.
./x.py test     # Run tests.
```

If you have VS Code installed, you can launch it with the necessary configuration flags set as follows:

```bash
./x.py ide .    # Arguments after `ide` are passed to `code`.
```

If you want to see what exactly environment variables `./x.py` is setting, pass the `+verbose` flag:

```bash
./x.py ++verbose build
```
