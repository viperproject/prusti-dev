============
Using Prusti
============

The link to the ZIP file containing the virtual machine was removed for
double blind review.

I. Virtual Machine
------------------

The ZIP file contains a VirtualBox image with Ubuntu that has Prusti
installed as a command line tool. To start the virtual machine, follow
these steps:

1.  Download and install VirtualBox from https://www.virtualbox.org/.
2.  Extract the ZIP archive.
3.  Start VirtualBox.
4.  Choose File → Import VM...  (Import Appliance... on Mac).
5.  Select the extracted Prusti.ova file and follow the instructions.

If the import was successful, there should be *Prusti* in the list of
virtual machines. Select it and click Start. The OS should log in
without asking for password. In case you need it, the user is called
prusti and the password is also prusti.

II. Trying Examples
-------------------

On the desktop there is a folder called ``Prusti Examples``. For each
example we verified, it contains two files: the original Rust file
``*.rs.orig`` and the verified version ``*.rs``. For example, the
original version of the binary search example can be found in file
``Binary_search.rs.orig`` and the verified version in file
``Binary_search.rs``. Each ``*.rs`` file has a comment that explains
from where exactly the example was taken and lists the changes made to
the example, as well as the verified properties.

You can run Prusti on an example as follows:

1.  Open the terminal.
2.  Change the current directory to the examples directory:

        cd "Desktop/Prusti Examples"

3.  Run Prusti on a chosen example::

        prusti borrow_first.rs

    Note that for examples that have an empty main function, Prusti will
    emit warnings about unused functions and structs. This is expected
    and does not influence verification.

4.  The last message printed by Prusti will be the verification
    outcome, which for ``borrow_first.rs`` would be *Successful
    verification of 3 items*.

5.  To see how Prusti reports errors, try commenting out part of the
    specification or introducing a bug. For instance, the
    ``borrow_first_missing_spec.rs`` example is equivalent to the
    previous one just with one of the preconditions commented out. If
    you ran prusti on it, it will report a verification error::

        prusti borrow_first_missing_spec.rs

        error[P0011]: precondition might not hold.
          --> ../artifact/examples/borrow_first_missing_spec.rs:84:13
           |
        84 |     let r = vec.borrow(0);  // This will panic if the vector is empty.
           |             ^^^^^^^^^^^^^

        Verification failed
        error: aborting due to previous error

6.  You can enable overflow checks by setting the environment variable
    PRUSTI_CHECK_BINARY_OPERATIONS to ``true``::

        PRUSTI_CHECK_BINARY_OPERATIONS=true prusti Heapsort.rs

    Since the Heapsort specifications are too weak to prove absence of
    overflows, Prusti will report two errors::

        error[P0007]: assertion might fail with "attempt to subtract with overflow"
           --> ../artifact/examples/Heapsort.rs:125:9
            |
        125 |         start -= 1;
            |         ^^^^^^^^^^

        error[P0007]: assertion might fail with "attempt to add with overflow"
           --> ../artifact/examples/Heapsort.rs:159:16
            |
        159 |             if child + 1 <= end && order(*array.borrow(child), *array.borrow(child + 1)) {
            |                ^^^^^^^^^

        Verification failed
        error: aborting due to 2 previous errors


7.  Similarly, you can disable the panic checks by setting
    PRUSTI_CHECK_PANICS to ``false``::

        PRUSTI_CHECK_PANICS=false prusti Heapsort.rs

    (No verification error will be reported in this case.)
