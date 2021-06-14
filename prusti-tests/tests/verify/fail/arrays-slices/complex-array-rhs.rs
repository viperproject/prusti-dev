fn main() {
    let mut a = [0; 3];
    a[0] += 1;  //~ ERROR array indexing is not supported in arbitrary operand positions yet
}
