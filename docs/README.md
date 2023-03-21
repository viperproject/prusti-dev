# Documentation

This is the source directory for Prusti's GitHub page (<https://viperproject.github.io/prusti-dev/>). Modifications should consist of pushes or pull requests to the `master` branch. Deployment on the `gh-pages` branch is done automatically via GitHub actions.

The books in this documentation use [mdbook](https://rust-lang.github.io/mdBook/index.html).

## Showing the book locally

After [installing mdbook](https://rust-lang.github.io/mdBook/guide/installation.html) and cloning the docs onto your machine, go to the book directory you want to work on.

By running `mdbook serve --open` (`mdbook.exe` on Windows), mdbooks will build the book and open it in your default browser.
On a file change, mdbook will rebuild the book and the browser window should refresh.


## Importing code files into the book

Small code samples can be immediately put into a code block inline to the book.
Larger code samples and code that should be checked by Prusti for correctness should be put into the prusti testing directory (`../prusti-tests/tests/`).

There you can put them in the corresponding directory, like is already done in `/verify/pass/user-guide/`.
These files will be automatically tested by the Prusti test-suite.

Code blocks that are not supposed to be run by a user, please add `noplaypen` to the code block.

To test all code imported into the documentation (in this case the user guide tutorial), you can run this command:
- `./x.py test -p prusti-tests --test compiletest -- user-guide`
This will attempt to verify all the Prusti examples in the `prusti-tests` directory that have the string "user-guide" in their path.


## Doctests

The final book can be tested using `mdbook test` (see [here](https://rust-lang.github.io/mdBook/cli/test.html)).
This will compile and run your code samples using **standard rustc** (no Prusti).

Code blocks that are not intended to be compiled should be marked with `ignore`.
Code blocks that should not run during doctests should be marked with `no_run`.

See more on documentation tests [here](https://doc.rust-lang.org/rustdoc/write-documentation/documentation-tests.html).

Doctests should also run automatically as part of the Prusti CI.

To run doctests locally with code that uses `prusti_contracts`, you will have to supply mdbook with a path containing the needed dependencies.
One (not very nice way) to do this, is taking any Rust crate that uses `prusti_contracts`, building it, then passing the path to that crate to mdbook: `mdbook test -L "(Path_to_crate)/target/debug/deps/"`

The crate `docs/dummy` is provided just to provide the dependencies.
To run the doctests (in this case for the user guide):
- `cd docs/dummy/`
- `cargo build`
- `cd ../user-guide/`
- `mdbook test -L ../dummy/target/debug/deps/`
