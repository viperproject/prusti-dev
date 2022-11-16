fn main() {
    let mut x = 'a';
    x = 'x';
    match x {
        'a' => assert!(false),
        'b' => assert!(false),
        'z' => assert!(false),
        'x' => {} // Ok
        _ => unimplemented!(),
    }
}
