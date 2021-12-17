fn looping() {
    let mut a = [0; 3];
    let mut i = 0;

    while i < 3 {
        a[i] = a[i];
        i += 1;
    }

    assert!(a[0] == 0);
}
