fn fail() {
    assert_eq!(1, 8);
}

fn fail2() {
    let x = 5;
    let y = 4 - 1;
    assert_eq!(x, y);
}