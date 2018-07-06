extern crate prusti_contracts;

fn diverging() -> ! {
    // This error should be reported
    loop {}
}

fn main() {
    diverging();
    // The return type is `Never`, so Prusti should assume `false` here.
    // The following assertion should not raise verification errors
    assert!(1 == 2);
}
