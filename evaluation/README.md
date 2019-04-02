Evaluation
==========

Lists all the functions and methods in a crate that can be verified in Prusti.

Note: this crate does not verify code.

Usage
-----

(from the `evaluation` folder)

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

Examples we could try to verify with some functional spec:

+   ackermann-function https://rosettacode.org/wiki/Ackermann_function#Rust
    **Properties:**
    +   termination
+   https://rosettacode.org/wiki/fibonacci_sequence#rust
    **Properties:**
    +   termination
    +   equivalence to a pure function
    **Changes:**
    +   Wrap types.
    +   Change the shape of a loop.
+   https://rosettacode.org/wiki/Binary_search#Rust binary-search
    **Changes:**
    +   Wrap types.
    +   Remove the ``return`` statement from the loop out.
    **Properties:**
    +   termination
    +   the vector indeed contains the searched element at the returned index.
+   heapsort https://rosettacode.org/wiki/Sorting_algorithms/Heapsort – uses
    slices, closures,
    **Changes:**
    +   Wrap types.
    **Properties:**
    +   termination
    +   the resulting array is sorted

Examples for which we could verify some functional properties, but is
not worth (because already covered by other examples):

+   https://rosettacode.org/wiki/Mutual_recursion#Rust
+   https://rosettacode.org/wiki/Factorial#Rust
+   https://rosettacode.org/wiki/Sorting_algorithms/Selection_sort#Rust
    – uses arrays and for loops.
+   sorting-algorithms/gnome-sort – uses vectors.
+   quicksort
    https://rosettacode.org/wiki/Sorting_algorithms/Quicksort#Rust –
    uses slices.
+   function-definition
    https://rosettacode.org/wiki/Function_definition#Rust – multiply two
    numbers.

Examples for which we could verify permissions:

+   tic_tac_toe
    **Changes:**
    +   Wrap types.
    +   Remove IO code.
+   taxicab_numbers – uses many unsupported constructs, which should be
    possible to change.
+   langtons-ant https://rosettacode.org/wiki/Langton%27s_ant#Rust –
    uses bit operations, vectors of vectors.
+   four-bit-adder – uses slices of arrays.
    https://rosettacode.org/wiki/Four_bit_adder
+   https://rosettacode.org/wiki/Knuth_shuffle#Rust – uses random
    numbers.
+   100-doors https://rosettacode.org/wiki/100_doors#Rust – uses arrays.
+   knuth-shuffle https://rosettacode.org/wiki/Knuth_shuffle – focus to
    shuffle an array.
+   knights-tour https://rosettacode.org/wiki/Knight%27s_tour#Rust –
    uses vectors.
+   dijkstras-algorithm
    https://rosettacode.org/wiki/Dijkstra%27s_algorithm#Rust – uses a
    vector and a binary heap.
+   forest-fire
    https://rosettacode.org/wiki/Forest_fire#Rust – uses vectors and
    iterators, but no closures.
+   https://rosettacode.org/wiki/Determine_if_only_one_instance_is_running#Rust
    – main functionality is to use a tcp socket.

Examples that use too many unsupported features (uses floats / uses bit
operations / uses Strings / closures / focuses on implementing traits /
focuses on IO / uses concurrency) or features that SMT solvers cannot
handle well (non-linear arithmetic):

+   24-game https://rosettacode.org/wiki/24_game#Rust – uses vectors,
    chars, strings, but only one closure. **potentially patchable**
+   https://rosettacode.org/wiki/24_game/Solve#Rust – uses slices,
    strings, but only one closure. **potentially patchable**
+   bitmap https://rosettacode.org/wiki/Bitmap/Write_a_PPM_file – uses
    vectors and non-linear arithmetic. **potentially patchable**
+   rot-13 https://rosettacode.org/wiki/Rot-13#Rust – uses strings,
    vectors, and iterators.
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

Verify supported functions from top 500 crates (option A)
---------------------------------------------------------

(from the `prusti-dev` folder)

1.  Download most popular 500 crates:

    ```bash
    evaluation/script/download-top-500.sh ../crates
    ```

2. Compile and run the evaluation on all the crates

	```bash
	evaluation/script/evaluate-all-crates.sh ../crates
	```

3. A report will be automatically displayed at the end, and stored at `../crates/evaluation-report-[date]-[time].log`

### Optional steps:

-  To compile and run the evaluation on a single crate

	```bash
	evaluation/script/evaluate-crate.sh ../crates/name_of_the_crate/
    ```

-  To generate the evaluation report manually:

	```bash
	evaluation/script/analyze-evaluation.sh ../crates
	```

### Examples

```bash
EVALUATION_TIMEOUT=1800 \
./evaluation/script/evaluate-all-crates.sh ../crates/
```

```bash
BASELINE_EVALUATION=false \
PRUSTI_CHECK_PANICS=true \
PRUSTI_CHECK_BINARY_OPERATIONS=true \
FINE_GRAINED_EVALUATION=true \
EVALUATION_TIMEOUT=900 \
MAX_PARALLEL_EVALUATIONS=4 \
./evaluation/script/evaluate-all-crates.sh ../crates/
```

Verify supported functions from top 500 crates (option B)
---------------------------------------------------------

(from the `prusti-dev` folder)

1.  Download most popular 500 crates:

    ```bash
    evaluation/script/download-top-500.sh ../crates
    ```

2. Compile and run the evaluation on all the crates

	```bash
	evaluation/script/full-evaluation.sh ../crates
	```

Verify supported functions from top 500 crates (option C)
---------------------------------------------------------

(from the `prusti-dev` folder)

2. Set variables

    ```bash
    export VIPER_HOME="$(realpath ../viper)"
    export Z3_EXE="$(realpath ../z3/bin/z3)"
    export RUSTC_TIMEOUT=900
    export PRUSTI_TIMEOUT=3600
    export CRATE_DOWNLOAD_DIR="$(realpath ../crates)"
    ```

2.  Download most popular 500 crates:

    ```bash
    evaluation/script/download-top-500.sh "$CRATE_DOWNLOAD_DIR"
    evaluation/script/set-cargo-lock.sh "$CRATE_DOWNLOAD_DIR"
    ```

3.  Compile crates:

    ```bash
	evaluation/script/compile-crates.sh" "$CRATE_DOWNLOAD_DIR" "$RUSTC_TIMEOUT"
    ```

4.  Filter crates:

    ```bash
	evaluation/script/filter-crates.sh "$CRATE_DOWNLOAD_DIR" \
        "$CRATE_DOWNLOAD_DIR/supported-crates.csv" "$PRUSTI_TIMEOUT"
	evaluation/script/whitelist-crates.sh "$CRATE_DOWNLOAD_DIR" \
        "$CRATE_DOWNLOAD_DIR/supported-crates.csv" "$PRUSTI_TIMEOUT"
    ```

5.  Verify all supported functions in crates:

    ```bash
    evaluation/script/verify-crates-coarse-grained.sh "$CRATE_DOWNLOAD_DIR" \
        "$CRATE_DOWNLOAD_DIR/supported-crates.csv" \
		"supported-procedures.csv" "$PRUSTI_TIMEOUT"
    ```

6.  Individually verify each supported functions with assertions:

    ```bash
    evaluation/script/verify-crates-coarse-grained.sh "$CRATE_DOWNLOAD_DIR" \
        "$CRATE_DOWNLOAD_DIR/supported-crates.csv" \
		"supported-procedures.csv" "$PRUSTI_TIMEOUT"
    ```
