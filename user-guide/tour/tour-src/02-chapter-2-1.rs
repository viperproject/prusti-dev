/*
    Chapter 2.1 - Basic Data Layout

error[E0072]: recursive type `List` has infinite size
  --> .\01-chapter-2-1.rs:12:1
   |
12 | pub enum List {
   | ^^^^^^^^^^^^^ recursive type has infinite size
13 |     Empty,
14 |     Elem(i32, List),
   |               ---- recursive without indirection
   |
help: insert some indirection (e.g., a `Box`, `Rc`, or `&`) to make `List` representable
   |
14 |     Elem(i32, Box<List>),
   |  

    [Module std::boxed](https://doc.rust-lang.org/std/boxed/index.html):
        > Box<T>, casually referred to as a ‘box’, provides the simplest form of heap allocation in Rust. 
        > Boxes provide ownership for this allocation, and drop their contents when they go out of scope. 
*/


pub enum List {
    Empty,
    Elem(i32, Box<List>),
}

/*
    Rust tutorial: Hey it built! ...but this is actually a really foolish definition of a List

    Notation: [] = Stack () = Heap

    A list with three elements looks as follows:
  
        > [Elem A, ptr] -> (Elem B, ptr) -> (Elem C, ptr) -> (Empty *junk*)
    
    - The last node is just overhead, the first node is not on the heap
    - Empty consumes space for a full pointer and an element

    This propagates e.g. when splitting off C:

        > [Elem A, ptr] -> (Elem B, ptr) -> (Empty *junk*)
        > [Elem C, ptr] -> (Empty *junk*)

    We would rather like to have a Java/C-style pointer that is nullable:

        > [ptr] -> (Elem A, ptr) -> (Elem B, ptr) -> (Elem C, *null*)

    Splitting off C then yields:

        > [ptr] -> (Elem A, ptr) -> (Elem B, *null*)
        > [ptr] -> (Elem C, *null*)

    Rust optimises the layout of enums such that the junk node (Empty) causes no overhead if the enum has the form

    > enum Foo {
    >    A,
    >    B(ContainsANonNullPtr),
    > }

    To profit from this null pointer optimisation, we thus move all data of a list node into a single C-style struct.
*/
