fn main() {
    let mut x = Vec::new();
    x[2] = 5; //~ ERROR: precondition might not hold
}
