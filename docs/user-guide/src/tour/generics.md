# Making it all Generic

> **Recommended reading:** 
> [3.2: Generic](https://rust-unofficial.github.io/too-many-lists/second-generic.html)

Just like the corresponding chapter in the "Learning Rust With Entirely Too Many Linked Lists" book, we will change our list to have a generic element type `T`, not just `i32`. For this, we go through our code an add the generic parameter `T` where required. The compiler really helps for this, since it will mark where a generic parameter is needed.
If you do this process with Prusti, at some point you will encounter the following error:
```plain
[E0369] binary operation `==` cannot be applied to type `T`.
```
This is because the generic type `T` might not implement [`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) and thus not have an equality function `==` that could be called on it like `i32` does. Since we only used `==` inside of specifications, we can fix this problems by using [snapshot equality `===`](../syntax.md#snapshot-equality) instead.

Here you can see where some of the changes were done (expand to see the full changes):

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/generic.rs:generic_types}}
```

This code still fails to compile, this time with an error from the function `link_lookup`:
```plain
[E0507] cannot move out of `node.elem` which is behind a shared reference.
[Note] move occurs because `node.elem` has type `T`, which does not implement the `Copy` trait
```

To fix this, we will change `List::lookup` and `link_lookup` to return a reference to the element at index `i`, instead of the element itself. This was not needed for `i32`, since it implements the [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) trait. For a general type `T`, returning it by value would move it out of the list, which we don't want. By returning a reference instead, the lookups will work for any type `T`, because the element stays in the list.

In addition to returning a reference, we will have to adjust some of the places where `lookup` is used, mostly by dereferencing or using `snap` on the returned reference:

```rust,noplaypen
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/generic.rs:lookup_reference}}
```

After all these changes, Prusti is able to verify the code again, so now our linked list can be used to store elements of any type, not just `i32`!
If you want to see the full code after all the changes, expand the following code block.

```rust,noplaypen
// Expand to see full code up to this chapter
{{#rustdoc_include ../../../../prusti-tests/tests/verify/pass/user-guide/generic.rs:nothing}}
```