# Peek

> **Recommended reading:** 
> [3.3: Peek](https://rust-unofficial.github.io/too-many-lists/second-peek.html)

Ideally, we could implement `peek` and `try_peek` like we implemented `pop` and `try_pop` before. This is currently not possible in Prusti, since structures containing references are not supported at the moment.
The return type of `try_peek` is `Option<&T>`, which is not supported.

We can still implement `peek` though, we just cannot do it by using `try_peek` like before:


**TODO**
