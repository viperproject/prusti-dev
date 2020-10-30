# Absence of panics

With the default settings, Prusti checks absence of panics. For example, consider the following program which always panics when executed:

```rust
pub fn main() {
    unreachable!();
}
```

When run on the previous program, Prusti reports a verification error:

```plain
error[P0004]: unreachable!(..) statement might be reachable
 --> src/lib.rs:2:5
  |
2 |     unreachable!();
  |     ^^^^^^^^^^^^^^^
  |
```

This message correctly points out that the `unreachable!()` statement might actually be reachable.

The message says "might" because by design Prusti is conservative, so it reports a verification error *unless* it can prove that the statement is unreachable, like in the following example:

```rust
pub fn main() {
    let a = 5;
    if a <= 0 {
        unreachable!();
    }
}
```

In this program, Prusti proves that the condition of the `if` branch is `false`, so no verification error is reported.

Since Prusti is conservative, if it reports no verification errors then it means that the program is provably correct with regard to the checked properties.
