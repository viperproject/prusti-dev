# Doctests Pipeline

This directory contains scripts to test Prusti on the standard library doctests:

- `run_doctests.py` is the executable script to run the pipeline and analyze the results
- `analysis.py` contains rules for categorization of test failures

## Summary

The Rust standard library contains doctests.
These are executable code snippets inside documentation comments of the standard library.
We can extract these tests and have Prusti run on them.

Since the standard library was written without Prusti in mind, we don't actually care about verification results.
However, by observing Prusti outputs, we can analyze Prusti's support for features inside the standard library.

`run_doctests.py` extracts the tests from standard library source code, checks whether they run successfully and runs Prusti on them.
Results are stored in a SQLite database that is later read for analysis.

In CI, there is a job running `run_doctests.py ci` which runs the tests, prints an immediate analysis and discards the database.
By default, tests in the `alloc` and `core` crates are used.
However, the script can be run manually as well.

Running `./run_doctests.py --help` shows a comprehensive help menu.
If not running `full` or `ci`, the steps should be run in the following order:

- (optional) `snapshot`: Build Prusti and create a self-contained snapshot directory
- `extract`: Extract doctests from Rust source files
- `compile`: Compile extracted `.rs` snippets with `rustc`
- `copy-passing`: Copy snippets that compiled and ran successfully to a new directory
- `prusti`: Run `prusti-rustc` on snippets
- `analyze`: Analyze a Prusti results database and print categorized summary.

We recommend using `uv` to run the script to automatically install dependencies, like `uv run run_doctests.py`.