fn main() {
    let a = [0; 3];
    let b: &[_] = &a;
    let c: &[_] = &a;
    
    assert!(b == c);
}
