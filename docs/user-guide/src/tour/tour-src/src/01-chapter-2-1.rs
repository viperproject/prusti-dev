/*
    Capter 2 - A Bad Singly-Linked Stack

    Chapter 2.1 - Basic Data Layout

    > List a = Empty | Elem a (List a)

    A list is a sum type (Rust: enum)  

    For now, we only support storing 32-bit integers
*/

// pub allows using List outside this module (not necessary here)
pub enum List {
    Empty,
    Elem(i32, List),
}
