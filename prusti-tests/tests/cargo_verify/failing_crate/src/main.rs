mod utils;

use utils::requires_large_number;

fn bad_client() {
    requires_large_number(10);
}

fn main() {
    assert!(true);
}
