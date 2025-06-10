use prusti_contracts::*;

trait Foo: Sized {
    #[requires(x > 5)]
    fn baz(self, x: u32) -> u32;
}

fn go<T: Foo>(t: T) -> u32 {
    t.baz(2) //~ ERROR: precondition might not hold
}

fn main(){

}
