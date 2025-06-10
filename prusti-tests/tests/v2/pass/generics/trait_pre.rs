use prusti_contracts::*;

trait Foo: Sized {
    #[requires(x > 5)]
    fn baz(self, x: u32) -> u32;
}

impl Foo for u32 {
    fn baz(self, x: u32) -> u32 {
        check(x);
        0
    }
}

#[requires(x > 2)]
fn check(x: u32) {
}


fn go<T: Foo>(t: T) -> u32 {
    t.baz(7)
}

fn main(){

}
