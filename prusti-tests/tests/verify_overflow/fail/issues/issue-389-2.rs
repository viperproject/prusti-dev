fn foo() {}

fn bar(mut i: i32) {
    while {
        i += 1; //~ ERROR attempt to add with overflow
        i > 0
    } {
        foo();
    }
}

fn main() {}
