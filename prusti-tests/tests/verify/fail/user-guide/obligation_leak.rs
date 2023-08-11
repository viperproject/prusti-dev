//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
obligation! {
    fn alloced(amount: usize, loc: usize);
}

#[trusted]
#[ensures(alloced(1, result))]
fn alloc() -> usize {
    unreachable!() // <- this would be a foreign function call to allocate an object
}

#[trusted]
#[requires(alloced(1, loc))]
fn dealloc(loc: usize) {
    unreachable!() // <- this would be a foreign function call to deallocate an object
}

#[trusted]
#[requires(alloced(1, loc))]
#[ensures(alloced(1, loc))]
fn read_value(loc: usize) -> i32 {
    unreachable!() // <- this would be a foreign function call to read the value of an object
}

#[trusted]
#[requires(alloced(1, loc))]
#[ensures(alloced(1, loc))]
fn write_value(loc: usize, new_value: i32) {
    unreachable!() // <- this would be a foreign function call to write a value to an object
}

fn procedure1() {
    let obj_loc = alloc();
    let old_value = read_value(obj_loc);
    let new_value = if old_value > 0 {
        old_value - 1
    } else {
        0
    };
    write_value(obj_loc, new_value);
    dealloc(obj_loc);
}

fn procedure2() { //~ ERROR function might leak instances of obligation `alloced`
    let obj_loc = alloc();
    let old_value = read_value(obj_loc);
    if old_value <= 0 {
        return;
    }
    write_value(obj_loc, old_value - 1);
    dealloc(obj_loc);
}
//// ANCHOR_END: code
