use prusti_contracts::*;
trait Foo {
    #[ensures(false)] //~ ERROR: postcondition might not hold
    fn bar(){

    }
}

fn main(){}
