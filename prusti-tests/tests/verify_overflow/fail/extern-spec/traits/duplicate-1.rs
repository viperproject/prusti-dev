use prusti_contracts::*;

trait MyTrait {
    #[requires(true)]
    fn foo(&mut self) -> i32;
}

#[extern_spec]
trait MyTrait {
    #[trusted]
    #[requires(true)]
    fn foo(&mut self) -> i32; //~ ERROR: external specification provided for MyTrait::foo, which already has a specification
}

fn main() {

}