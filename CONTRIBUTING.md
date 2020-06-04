Running tests
=============

- Run `make test` to run all tests.


Filtering tests
---------------

- Set environment variable `TESTNAME` to a string. Then, the tests containing this string in its name are filtered.
- Run `make test-examples` to run those tests.
- Example: `TESTNAME=tree; make test-examples` runs only tests containing `tree` in its name.
