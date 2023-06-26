# Peek

> **Recommended reading:** 
> [3.3: Peek](https://rust-unofficial.github.io/too-many-lists/second-peek.html)

Ideally, we could implement `peek` and `try_peek` like we implemented `pop` and `try_pop` before. Like `pop`, `push` can only be called if the list is non-empty, and it then always returns a reference to the element at the head of the list (type `&T`). Similarly, `try_peek` can be called on any list, but returns an `Option<&T>`. The latter is currently not possible in Prusti, since structures containing references are not supported at the moment.

<!-- TODO: link capabilities/limitations chapter (refs in structs) -->

We can still implement `peek`, but we just cannot do it by using `try_peek` like before in `pop`. Instead, we can reuse the already implemented and verified `lookup` function! Since `lookup` can return a reference to any element of the list, we can just call `self.lookup(0)` inside of `peek`: 

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/peek.rs:implementation}}
```

We can also write a test again, to see if our specification holds up in actual code:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/peek.rs:test_peek}}
```

This verifies too, so it appears our implementation of `peek` is correct.

The `peek` method only returns an immutable reference, but what if you want to get a mutable reference? We will see how in the next chapter.

Here you can see the full code we have now:
```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/peek.rs:nothing}}
```