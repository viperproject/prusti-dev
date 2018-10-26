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

Patchable(?) examples:

+   tic_tac_toe – uses ``char``.
+   taxicab_numbers – uses many unsupported constructs, which should be
    possible to change.
+   https://rosettacode.org/wiki/Langton%27s_ant – uses bit operations,
    vectors of vectors.
+   four-bit-adder – uses slices of arrays.
    https://rosettacode.org/wiki/Four_bit_adder
+   https://rosettacode.org/wiki/Sorting_algorithms/Heapsort – uses
    slices, closures,
+   https://rosettacode.org/wiki/Sorting_algorithms/Selection_sort#Rust
    – uses arrays and for loops.
+   https://rosettacode.org/wiki/Knuth_shuffle#Rust – uses random
    numbers.

Hard to patch examples:

Not supported examples:

+   define_a_primitive_data_type – focusses on implementing many
    **standard** traits.
+   modular-exponentiation – uses arbitrary precision number library and
    non-linear arithmetic.
+   metered-concurrency – custom implementation of a counting semaphore.

Not interesting examples:

+   https://rosettacode.org/wiki/Determine_if_only_one_instance_is_running#Rust
    – main functionality is to use a tcp socket.
+   anonymous_recursion – demonstrates nested functions.
+   https://rosettacode.org/wiki/Rock-paper-scissors#Rust – uses slices,
    a random number generator, **IO is the central part**.
+   wireworld – uses chars, slices, **closures, IO is quite central**.
    https://rosettacode.org/wiki/Wireworld
+   conways_game_of_life – uses chars, slices, **closures, IO is quite central**.
    https://rosettacode.org/wiki/Conway%27s_Game_of_Life
+   https://rosettacode.org/wiki/Unbias_a_random_generator#Rust –
    focuses on random number generation.

Examples that use borrows:

+   bitmap, floyd_warshall_algorithm, 2048 – use to implement `index`
    and `index_mut`.
+   9_billion_names_of_god_the_integer – non trivial getters that are
    used in trivial ways.
+   menu – borrows self and returns a borrow of a string.
+   four_bit_adder – deref implementation.
+   strip_comments_from_a_string – reborrows a substring (uses closures)

Verify supported functions
--------------------------

1. Verify all the supported function in a given crate:

   ```bash
   bash scripts/verify-supported.sh path/to/the/crate
   ```
