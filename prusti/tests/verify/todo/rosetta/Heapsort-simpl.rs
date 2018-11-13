/// An adaptation of the example from
/// https://rosettacode.org/wiki/Sorting_algorithms/Heapsort#Rust

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    pub fn borrow(&mut self, index: usize) -> &mut i32 {
        self.v.get_mut(index).unwrap()
    }
}

#[pure]
fn order(x: &mut i32, y: &mut i32) -> bool {
    *x < *y
}

fn main() {}

fn shift_down(array: &mut VecWrapperI32, start: usize, end: usize)
{
    while true {
        let x = order(array.borrow(start), array.borrow(start));
    }
}
