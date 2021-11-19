fn foo() {}

fn bar(mut i: i32) {
    while {
        i += 1;
        i > 0
    } {
        foo();
    }
}

fn main() {}
