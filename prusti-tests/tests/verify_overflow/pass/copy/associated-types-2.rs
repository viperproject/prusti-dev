use prusti_contracts::*;

trait Foo {
    type Type;

    #[trusted]
    #[pure]
    fn foo(&self) -> Self::Type {
        unimplemented!()
    }
}

fn main() {

}