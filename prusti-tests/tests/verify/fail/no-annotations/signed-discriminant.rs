
#[derive(Copy, Clone)]
enum SignedEnum {
    A = -2,
    B,
    C,
}

fn test_ok_1() {
    let x = SignedEnum::A;

    if let SignedEnum::A = x {
        // Ok
    } else {
        unreachable!() // Ok
    }
}

fn test_ok_2(x: SignedEnum) {
    if let SignedEnum::A = x {
        // Ok
    } else {
        match x {
            SignedEnum::B => {} // Ok
            SignedEnum::C => {} // Ok
            _ => unreachable!() // Ok
        }
    }
}

fn test_err() {
    let x = SignedEnum::A;

    if let SignedEnum::A = x {
        panic!() //~ ERROR panic!(..) statement might be reachable
    } else {
        // Nothing
    }
}

fn main() { }
