use prusti_contracts::*;

#[requires(x >= 0)]
#[pure]
#[trusted]
fn sqrt(x: i32) -> u32 {
    1
}

#[trusted]
#[ensures(forall(|x: i32| if(x >= 0) {
    result == sqrt(x) + 1
} else {
    result == 1
}))]
fn go() -> u32{
    1
}

fn main(){}
