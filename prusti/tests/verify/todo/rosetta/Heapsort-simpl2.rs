/// An adaptation of the example from
/// https://rosettacode.org/wiki/Sorting_algorithms/Heapsort#Rust

extern crate prusti_contracts;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    // Encoded as body-less Viper function
    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn borrow(&mut self, index: usize) -> &mut i32 {
        self.v.get_mut(index).unwrap()
    }

    // Encoded as body-less Viper method
    #[trusted]
    #[requires="index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="self.lookup(index) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    #[ensures="self.lookup(old(self.len())) == value"]
    #[ensures="forall i: usize :: (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))"]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }

    #[trusted]
    pub fn swap(&mut self, index_a: usize, index_b: usize) {
        self.v.swap(index_a, index_b);
    }
}

#[pure]
fn order(x: i32, y: i32) -> bool {
    x < y
}

fn main() {
    let mut v = VecWrapperI32::new();
    v.push(4);
    v.push(6);
    v.push(8);
    v.push(1);
    v.push(0);
    v.push(3);
    v.push(2);
    v.push(2);
    v.push(9);
    v.push(5);
    heap_sort(&mut v);
}

fn heap_sort(array: &mut VecWrapperI32)
{
    let len = array.len();

    let mut start = len/2-1;
    let mut continue_loop = start >= 0;
    // Create heap
    while continue_loop {
        shift_down(array, start, len - 1);
        start -= 1;
        continue_loop = start >= 0;
    }

    let mut end = len-1;
    let mut continue_loop = end >= 1;
    while continue_loop {
        array.swap(0, end);             // TODO: Problematic line.
        //shift_down(array, 0, end - 1);  // TODO: Problematic line.
        end -= 1;
        continue_loop = end >= 1;
    }
}

fn shift_down(array: &mut VecWrapperI32, start: usize, end: usize)
{
    let mut root = start;
    let mut continue_loop = true;
    while continue_loop {
        let mut child = root * 2 + 1;
        if child > end {
            continue_loop = false;
        }
        else {
            if child + 1 <= end && order(*array.borrow(child), *array.borrow(child + 1)) {
                child += 1;
            }
            if order(*array.borrow(root), *array.borrow(child)) {
                array.swap(root, child);
                root = child
            } else {
                continue_loop = false;
            }
        }
    }
}
