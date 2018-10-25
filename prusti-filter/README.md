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
