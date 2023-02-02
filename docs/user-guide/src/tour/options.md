# Options

> **Recommended reading:** 
> [3: An Ok Single-Linked Stack](https://rust-unofficial.github.io/too-many-lists/second.html),
> [3.1. Option](https://rust-unofficial.github.io/too-many-lists/second-option.html)

Just like in the "Learning Rust With Entirely Too Many Linked Lists" tutorial, we can change our `enum Link` to use the `Option` type via a type alias instead of manually implementing `Empty` and `More`:

```rust,noplaypen,ignore
type Link = Option<Box<Node>>;
```

In order to use the `Option::take` and the `Option::map` function, we also have to implement the `extern_spec` for them:

```rust,noplaypen

```

These changes require some adjustments of the code and specifications:

```rust,noplaypen

```