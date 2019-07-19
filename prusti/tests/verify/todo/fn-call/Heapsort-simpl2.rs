/// An adaptation of the example from
/// https://rosettacode.org/wiki/Sorting_algorithms/Heapsort#Rust

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    pub fn swap(&mut self, index_a: usize, index_b: usize) {
        self.v.swap(index_a, index_b);
    }
}

fn heap_sort(array: &mut VecWrapperI32, b: bool)
{
    while b {
        array.swap(0, 0);
    }
}

fn main() { }
