use prusti_contracts::*;

pub fn test1<T: PartialEq>(container: &mut Option<T>, value: T) {
    let new_value = Some(value);
    if *container != new_value {
        *container = new_value;
    }
}

fn main() {}
