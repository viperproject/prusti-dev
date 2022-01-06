#[derive(Clone, Default)]
struct T {
    // Wrap in Box to have non-Copy types
    value1: Box<u32>,
    value2: Box<u32>,
    value3: Box<u32>,
}

#[analyzer::run]
fn main() {
    let mut x = T::default();
    // Move out value1
    drop(x.value1);
    // Block value2
    let borrow_value2 = &mut x.value2;
    let block_value2 = &borrow_value2;
    // Freeze value3
    let shared_ref = &x.value3;
    // Nothing should be owned here
    drop(shared_ref);
    // Now value3 should be owned
    drop(block_value2);
    // Now value2 should be owned
    x.value1 = Box::new(123);
    // Now everything should be owned
    drop(x);
    // Now the state should be empty
}
