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

Examples we could try to fully verify:

+   TODO

Examples for which we could verify permissions:

+   TODO

Examples that use too many unsupported features (iterators, closures,
bit-operators, floats, etc.) or features that SMT solvers cannot handle
well (non-linear arithmetic):

+   TODO

Encodable examples:

+   ackermann-function https://rosettacode.org/wiki/Ackermann_function#Rust
+   https://rosettacode.org/wiki/Fibonacci_sequence#Rust
+   https://rosettacode.org/wiki/Mutual_recursion#Rust
+   https://rosettacode.org/wiki/Factorial#Rust

Patchable(?) examples:

+   https://rosettacode.org/wiki/Binary_search#Rust binary-search – uses
    slices.
+   tic_tac_toe – uses ``char``.
+   taxicab_numbers – uses many unsupported constructs, which should be
    possible to change.
+   langtons-ant https://rosettacode.org/wiki/Langton%27s_ant – uses bit
    operations, vectors of vectors.
+   four-bit-adder – uses slices of arrays.
    https://rosettacode.org/wiki/Four_bit_adder
+   heapsort https://rosettacode.org/wiki/Sorting_algorithms/Heapsort – uses
    slices, closures,
+   https://rosettacode.org/wiki/Sorting_algorithms/Selection_sort#Rust
    – uses arrays and for loops.
+   https://rosettacode.org/wiki/Knuth_shuffle#Rust – uses random
    numbers.
+   100-doors https://rosettacode.org/wiki/100_doors#Rust – uses arrays.
+   knuth-shuffle https://rosettacode.org/wiki/Knuth_shuffle – focus to
    shuffle an array.
+   gnome-sort – uses vectors.
+   knights-tour https://rosettacode.org/wiki/Knight%27s_tour#Rust –
    uses vectors.
+   rot-13 https://rosettacode.org/wiki/Rot-13#Rust – uses strings,
    vectors, and iterators.
+   quicksort
    https://rosettacode.org/wiki/Sorting_algorithms/Quicksort#Rust –
    uses slices.
+   dijkstras-algorithm
    https://rosettacode.org/wiki/Dijkstra%27s_algorithm#Rust – uses a
    vector and a binary heap.
+   forest-fire
    https://rosettacode.org/wiki/Forest_fire#Rust – uses vectors and
    iterators, but no closures.

Hard to patch examples:

+   24-game https://rosettacode.org/wiki/24_game#Rust – uses vectors,
    chars, strings, but only one closure.
+   https://rosettacode.org/wiki/24_game/Solve#Rust – uses slices,
    strings, but only one closure.
+   bitmap https://rosettacode.org/wiki/Bitmap/Write_a_PPM_file – uses
    vectors and non-linear arithmetic.

Not supported examples:

+   define_a_primitive_data_type – focusses on implementing many
    **standard** traits.
+   rational https://rosettacode.org/wiki/Arithmetic/Rational#Rust –
    focusses on implementing many **standard** traits, uses non-linear
    arithmetic.
+   modular_exponentiation
    modular-exponentiation – uses arbitrary precision number library and
    non-linear arithmetic.
+   metered-concurrency – custom implementation of a counting semaphore.
+   zig-zag-matrix – uses iterators, closures, and non-linear arithmetic.
+   sudoku – uses iterators and closures extensively.
+   radix-sort – uses bit operations.
+   pancake-sort
    https://rosettacode.org/wiki/Sorting_algorithms/Pancake_sort#Rust –
    uses iterators and closures extensively.
+   iterated-digits-squaring
    https://rosettacode.org/wiki/Iterated_digits_squaring – use
    non-linear arithmetic.
+   digital-root https://rosettacode.org/wiki/Digital_root#Rust – use
    non-linear arithmetic.
+   bogosort
    https://rosettacode.org/wiki/Sorting_algorithms/Bogosort#Rust – use
    closures and iterators extensively.
+   2048 https://rosettacode.org/wiki/2048 – uses non-linear arithmetic,
    focuses on IO.
+   15-puzzle-game https://rosettacode.org/wiki/15_Puzzle_Game#Rust –
    uses random number generation, IO, iterators, and closures.
+   constrained-random-points-on-a-circle
    https://rosettacode.org/wiki/Constrained_random_points_on_a_circle#Rust
    – uses non-linear arithmetic.
+   sha-1 – uses bit operations.
+   the-isaac-cipher – uses bit operations.
+   s-expressions – extensive use of string manipulations and closures.

Not interesting examples:

+   https://rosettacode.org/wiki/Determine_if_only_one_instance_is_running#Rust
    – main functionality is to use a tcp socket.
+   anonymous_recursion – demonstrates nested functions.
+   rock_paper_scissors
    https://rosettacode.org/wiki/Rock-paper-scissors#Rust – uses slices,
    a random number generator, **IO is the central part**.
+   wireworld – uses chars, slices, **closures, IO is quite central**.
    https://rosettacode.org/wiki/Wireworld
+   conways-game-of-life – uses chars, slices, **closures, IO is quite central**.
    https://rosettacode.org/wiki/Conway%27s_Game_of_Life
+   https://rosettacode.org/wiki/Unbias_a_random_generator#Rust –
    focuses on random number generation.
+   function-definition
    https://rosettacode.org/wiki/Function_definition#Rust – multiply two
    numbers.
+   visualize-a-tree https://rosettacode.org/wiki/Visualize_a_tree#Rust
    – IO is the central part.

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

To verify all the supported procedures in a given crate:

```bash
bash scripts/verify-supported.sh path/to/the/crate
```

Alternativelly, to run the previous script on all the crates previously downloaded:

```bash
bash scripts/verify-all-supported-crates.sh path/to/the/crate/download/dir
```
