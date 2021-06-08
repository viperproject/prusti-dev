fn main() {
    let a  = 10. - 10.0000009;
    assert!(a < 0.);
}