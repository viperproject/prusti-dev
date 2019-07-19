extern crate prusti_contracts;

struct T(u32, i32);

impl Default for T {
    fn default() -> Self {
        panic!("Error message") //~ ERROR
    }
}

fn main() {}
