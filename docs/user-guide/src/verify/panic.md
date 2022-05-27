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

The message says "might" because Prusti is conservative, i.e., it reports a verification error *unless* it can prove that the statement is unreachable.
Hence, Prusti successfully the example below as it can rule out that the condition in the conditional statement, `a <= 0`, holds.

```rust
pub fn main() {
    let a = 5;
    if a <= 0 {
        unreachable!();
    }
}
```

Since Prusti is conservative, if it reports no verification errors then the program is provably correct *with regard to the checked properties.*
The last part is important because checks such as [overflow checks](overflow.html) may be disabled. 
Furthermore, Prusti may verify a program although some (or even all) of its executions do not terminate because it verifies partial correctness properties.
