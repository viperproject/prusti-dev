struct T(u32, i32);

impl Default for T {
    fn default() -> Self {
        panic!("Error message") //~ ERROR panic!(..) statement might be reachable
    }
}

fn main() {}
