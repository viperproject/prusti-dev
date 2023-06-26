# Options

> **Recommended reading:** 
> [3: An Ok Single-Linked Stack](https://rust-unofficial.github.io/too-many-lists/second.html),
> [3.1. Option](https://rust-unofficial.github.io/too-many-lists/second-option.html)

Just like in the "Learning Rust With Entirely Too Many Linked Lists" tutorial, we can change our `enum Link` to use the `Option` type via a type alias instead of manually implementing `Empty` and `More`:

```rust,noplaypen,ignore
type Link = Option<Box<Node>>;
```

In order to use the `Option::take` function, we also have to implement the `extern_spec` for it. As you can see, it is quite similar to the `extern_spec` for `mem::replace`, since `take` does the same as `replace(&mut self, None)`:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/option.rs:option_take_extern_spec}}
```

Changing the `Link` type requires some adjustments of the code and specifications. With the new type alias for `Link`, we cannot have an `impl Link` block anymore, so our `lookup` and `len` functions on `Link` are now normal, free-standing functions:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/option.rs:rewrite_link_impl}}
```

Due to current limitations of Prusti, we cannot replace our `link_len` and `link_lookup` functions with loops:

<!-- TODO: link capabilities/limitations chapter (loops in pure functions) -->

```rust,noplaypen,ignore
{{#rustdoc_include ../../../../prusti-tests/tests/verify/fail/user-guide/option_loops_in_pure_fn.rs:code}}
```

Since Prusti doesn't fully support closures yet, we also cannot do the rewrite to use the `Option::map` function:
```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/option.rs:try_pop_rewrite}}
```

After all the changes done in this chapter, Prusti is still be able to verify the code, so we didn't break anything.
If you want to see the full code after all the changes, expand the following code block.

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/option.rs:nothing}}
```