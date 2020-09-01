extern crate prusti_contracts;

trait MyTrait {
    fn foo(&self);
}

impl MyTrait for i64 {
    #[requires="true"]
    fn foo(&self) {}
}

fn main(){}
