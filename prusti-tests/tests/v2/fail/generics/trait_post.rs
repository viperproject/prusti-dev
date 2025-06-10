use prusti_contracts::*;

trait Foo: Sized {
    #[ensures(result == 5)] //~ ERROR: postcondition might not hold
    fn baz(self) -> u32;
}

impl Foo for u32 {
    fn baz(self) -> u32 {
        4
    }
}

#[ensures(result == 5)]
fn go<T: Foo>(t: T) -> u32 {
    t.baz()
}

fn main(){

}
