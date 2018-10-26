Prusti-filter
=============

Lists all the functions and methods in a crate that can be verified in Prusti.

Note: this crate does not verify code.

Usage
-----

1.  Download info about all crates:

    ```bash
    mkdir -p crates/index
    git clone https://github.com/rust-lang/crates.io-index.git crates/index
    python3 script/download-crate-info.py
    ```

2.  Download most popular 500 crates:

    ```bash
    python3 script/select-popular-crates.py ../../crates
    bash crates/download.sh
    ```

3.  Compile them:

    ```bash
    bash crates/analyse.sh
    ```

4.  Collect/analyse results:

    ```bash
    python3 script/collect-results.py ../../crates
    ```

Rosetta
-------

1.  Check tasks:

    ```bash
    python3 script/check-rosetta.py ../../
    bash rosetta/analyse.sh
    ```

2.  Collect/analyse results:

    ```bash
    python3 script/collect-results.py ../../rust-rosetta/tasks/
    python3 script/analyse-results.py
    ```

Encodable examples:

+   https://rosettacode.org/wiki/Ackermann_function#Rust
+   https://rosettacode.org/wiki/Fibonacci_sequence#Rust
+   https://rosettacode.org/wiki/Mutual_recursion#Rust
+   https://rosettacode.org/wiki/Factorial#Rust

Not interesting examples:

+   https://rosettacode.org/wiki/Determine_if_only_one_instance_is_running#Rust
    – main functionality is to use a tcp socket.
+   anonymous_recursion – demonstrates nested functions.

Patchable(?) examples:

+   tic_tac_toe – uses ``char``.
+   taxicab_numbers – uses many unsupported constructs, which should be
    possible to change.
+   https://rosettacode.org/wiki/Langton%27s_ant – uses bit operations,
    vectors of vectors.

Not supported examples:

+   define_a_primitive_data_type – implements many standard traits.

TODO: Checked up to 8'th position in min_size >= 5.

Verify supported functions
--------------------------

To verify all the supported procedures in a given crate:

```bash
bash scripts/verify-supported.sh path/to/the/crate
```

Alternativelly, to run the previous script on all the crates previously downloaded:

```bash
bash scripts/verify-all-supported-crates.sh path/to/the/crate/download/dir
```
