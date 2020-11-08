# Pure function encoding

To encode specifications and side-effect-free functions (marked with `#[pure]`), Prusti generates Viper [functions](http://viper.ethz.ch/tutorial/?page=1&section=#functions). A Viper function consists of a single expression, so Rust function bodies must be folded accordingly. This is only possible for loop-less functions.

For example, the Rust function:

```rust
#[pure]
fn hello(a: i32) -> i32 {
  let mut b = 10;
  if a < 3 {
    b = a + 2
  } else if a > 10 {
    b = a - 2
  }
  b
}
```

Is encoded as:

```viper
function hello(a: Int): Int
  requires true
{
  !(a < 3) ? (!(a > 10) ? 10 : a - 2) : a + 2
}
```

> - [`prusti-viper/src/encoder/mir_interpreter.rs` - `run_backward_interpretation`](https://github.com/viperproject/prusti-dev/blob/6e5d9e258c5d674bc0cd2f3d42c061ddf6409b1a/prusti-viper/src/encoder/mir_interpreter.rs#L35-L93) - backward state interpreter, used to determine if MIR has any loops.
> - [`prusti-viper/src/encoder/pure_function_encoder.rs`](https://github.com/viperproject/prusti-dev/blob/6e5d9e258c5d674bc0cd2f3d42c061ddf6409b1a/prusti-viper/src/encoder/pure_function_encoder.rs)
