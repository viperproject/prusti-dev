use prusti_contracts::*;

#[requires(forall(|t: &u32| (t != faulty_witness)))]
fn req(faulty_witness: &u32) {
}

fn main(){}
