Prusti-tests
============

Crate containing the end-to-end tests (input program and expected result) of Prusti.


The tests are organized into several categories under the `tests/` folder:

* `cargo_verify` is meant to test `cargo-prusti` and the `prusti-contracts` crate. It checks on a set of crates that (1) cargo build succeeds and (2) `cargo-prusti` produces the expected output.
* `parse` tests the parsing of specifications. This doesn't run the verifier.
* `typecheck` tests the type-checking of specifications. This doesn't run the verifier.
* `verify` runs the verifier with overflow checks disabled.
* `verify_overflow` runs the verifier with overflow checks enabled.
* `verify_partial` runs the verifier with overflow checks enabled, while testing the verifier with test cases that only partially verify due to known open issues. These tests are always linked to a Github issue. The purpose of these tests is two-fold: (1) these tests help prevent potential further regressions, because the tests also test code paths not covered by other tests; and (2) a failing test without any errors notifies the developer when a proper fix is in place. In this case, these test can be moved to the `verify/pass/` or `verify_overflow/pass` folders.
