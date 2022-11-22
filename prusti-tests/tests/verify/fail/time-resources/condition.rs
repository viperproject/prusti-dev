use prusti_contracts::*;

fn main() {
    if time_credits(42) || time_receipts(12) { //~ ERROR
        println!("foo");
    } else {
        println!("bar");
    }
}
