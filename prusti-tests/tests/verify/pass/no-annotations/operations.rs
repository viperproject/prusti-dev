fn main() {
    let a = 10;
    let b = (a + 2) - 6;  // 6
    let c = (b - 1) * 2;  // 10
    let d = -c;  // -10
    let x = (0 < d) || (d > 10);  // true
    let y = (10 >= d) && (d <= 0);  // false
    let z = (a == b) || (x != y); // true
    assert!(d == -10 && z);

    assert!(9 / 2 == 4);
}
