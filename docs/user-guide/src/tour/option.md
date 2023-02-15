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
{{#rustdoc_include tour-src/src/option/initial_code.rs:option_take_extern_spec}}
```

These changes require some adjustments of the code and specifications. With the new type alias for `Link`, we cannot have an `impl` block anymore, so our `lookup` and `len` functions on `Link` are now normal, non-associated functions:

```rust,noplaypen
{{#rustdoc_include tour-src/src/option/initial_code.rs:rewrite_link_impl}}
```

Due to current [limitations of Prusti](../limitations.md), we cannot replace our `len` and `lookup` functions with loops:

```rust,noplaypen,ignore
# use prusti_contracts::*;
# 
# pub struct List {
#     head: Link,
# }
# 
# type Link = Option<Box<Node>>;
# 
# struct Node {
#     elem: i32,
#     next: Link,
# }
# 
impl List {
    // Prusti cannot verify these functions at the moment,
    // since loops in pure functions are not yet supported:
    #[pure]
    pub fn len(&self) -> usize {
        let mut curr = &self.head;
        let mut i = 0;
        while let Some(node) = curr {
#             body_invariant!(true);
            i += 1;
            curr = &node.next;
        }
        i
    }

    #[pure]
    #[requires(index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        let mut curr = &self.head;
        let mut i = index;
        while let Some(node) = curr {
#             body_invariant!(true);
            if i == 0 {
                return node.elem;
            }
            i -= 1;
            curr = &node.next;
        }
        unreachable!()
    }
}
```

Since Prusti doesn't fully support closures yet, we also cannot do the rewrite to use the `Option::map` function:
```rust,noplaypen
{{#rustdoc_include tour-src/src/option/initial_code.rs:try_pop_rewrite}}
```

After all the changes done in this chapter, Prusti is still be able to verify the code, so we didn't break anything.
If you want to see the full code after all the changes, expand the following code block.

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include tour-src/src/option/initial_code.rs:nothing}}
```