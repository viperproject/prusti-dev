use prusti_contracts::*;
trait Foo {
    #[requires(x < 10)]
    #[ensures(result > x)]
    fn bar(x: u32) -> u32 {
        x + 1
    }
}

impl Foo for bool {}

#[ensures(result)]
fn client() -> bool {
    let x = 5;
    let y = bool::bar(x);
    y > x
}

fn main(){
}
