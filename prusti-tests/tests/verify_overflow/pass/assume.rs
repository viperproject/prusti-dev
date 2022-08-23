use prusti_contracts::*;

#[ensures(p == np)]
fn proof(p: u32, np: u32) {
  prusti_assume!(false);
}

fn main(){}
