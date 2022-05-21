# Basic Usage

## Prusti Assistant

When the Prusti Assistant extension is active, Rust files can be verified in one of the following ways:

- By clicking the "Verify with Prusti" button in the status bar.
- By opening the [Command Palette](https://code.visualstudio.com/docs/getstarted/userinterface#_command-palette) and running the command "Prusti: save and verify this file".
- By saving a Rust document, if "Verify on save" is enabled.
- By opening a Rust document, if "Verify on open" is enabled.

See the [following chapter](verify/summary.md) for a list of verification features available in Prusti.

## Command line

To run Prusti on a file using the command-line setup:

```bash
$ prusti-rustc --edition=2018 path/to/file.rs
```

## Introductory example

Let us verify that the function `max` below, which takes two integers and returns the greater one, is implemented correctly.

```rust
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}
```

When pasting the above code into a Rust file and then verifying it with Prusti (as outlined at the top of the page), Prusti should report that verification succeeded.
This tells us that

1. the file consists of valid Rust code that can be compiled successfuly, and
2. no execution reaches a Rust panic (explicit call of the [`panic!()`](https://doc.rust-lang.org/std/macro.panic.html) macro, a failed assertion, etc).

To also verify that `max` indeed always returns the maximum of its two inputs, we have to add a corresponding specification, which states
that the return value of `max` is at least as large as both `a` and `b` and, additionally, coincides with `a` or `b`:

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}
```

In the above program, the first two lines are required to enable Prusti-specific syntax for writing specifications:

- The first line, `extern crate prusti_contracts;`, is needed by Prusti to typecheck the specifications.
- The second line, `use prusti_contracts::*;`, allows us to write `#[ensures(...)]` instead of `#[prusti_contracts::ensures(...)]`.

> **Warning:** Due to limitations in Rust procedural macros, `use prusti_contracts::*;` should *always* be used, and the Prusti specification attributes should not be imported with an alias.

After that, we used `#[ensures(...)]` to attach two [postconditions](verify/prepost.md) to the function `max`. 
The syntax of specifications is a superset of Rust expressions, where `result` is a keyword referring to the function's return value. 

Again, verifying the above code with Prusti should succeed. 
Notice that Prusti assumes by default that integer types are bounded; it thus performs [overflow and underflow checks](verify/overflow.md) unless corresponding options are provided.

Next, we add a second function `max3` which returns the maximum of three instead of two integers; we reuse the already verified function `max` in the new function's specification to show that this function is implemented correctly.

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

#[ensures(result == max(a, max(b, c)))]
fn max3(a: i32, b: i32, c: i32) -> i32 {
    if a > b && a > c {
        a
    } else {
        if b > c {
            b
        } else {
            c
        }
    }
}
```

Again, Prusti should successfully verify the above program.
Notice that we additionally declared the function `max` as [pure](verify/pure.md) such that it can be used within specifications.
If we omit this annotation, Prusti will complain that the postcondition of function `max3` is invalid because it uses an `impure` function, which may potentially have side-effects.

So far, we only considered programs that meet their specification and that, consequently, Prusti successfully verified.
To conclude this example, assume we accidentally return `c` instead of `b` if `b > c` holds:

```rust
#[ensures(result == max(a, max(b, c)))]
fn max3(a: i32, b: i32, c: i32) -> i32 {
    if a > b && a > c {
        a
    } else {
        if b > c {
            c // ERROR
        } else {
            c
        }
    }
}
```

In this case, Prusti will highlight the line with the error and report that the `postcondition might not hold`.

For debugging purposes, it is often useful to add `assert!(...)` macros to our code to locate the issue. For example, in the code below, we added an assertion that fails because `b > c` and thus the maximum of `b` and `c` is `b` instead of `c`. 

```rust
extern crate prusti_contracts;
use prusti_contracts::*;

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

#[ensures(result == max(a, max(b, c)))]
fn max3(a: i32, b: i32, c: i32) -> i32 {
    if a > b && a > c {
        a
    } else {
        if b > c {
            assert!(max(b, c) == c); // FAILS
            c
        } else {
            c
        }
    }
}
```

When running Prusti on this example, it highlights the failing assertion and thus enables us to quickly locate and fix the issue. 

## Configuration

Prusti offers a many flags to configure its behavior. See [Providing Flags](https://viperproject.github.io/prusti-dev/dev-guide/config/providing.html) for how to provide these flags and [List of Configuration Flags](https://viperproject.github.io/prusti-dev/dev-guide/config/flags.html) in the developer guide.
