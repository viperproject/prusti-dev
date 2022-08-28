// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

#[print_counterexample("a = {}; b = {} = {} = b", a, b, b)]
struct X<T>{
    a: T, 
    b: i32,
}


#[print_counterexample("unnamed field of Y = {}", 0)]
struct Y(i32);


#[print_counterexample]
enum Z{
    #[print_counterexample("values: {}, {}, {}", g, h, i)]
    E {
        g: i32,
        h: i32,
        i: i32,
    },
    F(i32, i32),
    #[print_counterexample("not initialized")]
    NotInit,
}

#[ensures(!result)]
fn test1(x: X<i32>, a: i32, y: Y, z:Z) -> bool{
    prusti_assume!(a > 0);
    x.a + y.0 == a
}

#[ensures(result)]
fn test2(z: Z) -> bool{
    match z {
        Z::E{ g:1, h: 2, i:3 } => false,
        _ => true,
    }
}

fn main() {}