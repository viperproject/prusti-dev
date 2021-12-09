#[derive(Clone, Default)]
struct T {
    value1: u32,
    value2: u32,
    value3: u32,
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
    let shared_ref = &mut x.value3;
    // Nothing should be owned here
    drop(shared_ref);
    // Now value3 should be owned
    drop(block_value2);
    // Now value2 should be accessible
    x.value1 = 123;
    // Now everything should be owned
    drop(x);
    // Now the state should be empty
}
