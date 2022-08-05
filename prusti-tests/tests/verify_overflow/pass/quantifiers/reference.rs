use prusti_contracts::*;

// This pre-condition is unsatisfiable, but Prusti should not crash
#[requires(forall(|t: &u32| (t != faulty_witness)))]
fn req(faulty_witness: &u32) {
}

fn main(){}
