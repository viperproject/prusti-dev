extern crate prusti_contracts;

struct UnexpectedValue(u32);

#[pure]
fn is_ok<T>(x: &Result<T, UnexpectedValue>) -> bool {
    if let Ok(_) = x {
        true
    } else {
        false
    }
}

#[pure]
fn is_err<T>(x: &Result<T, UnexpectedValue>) -> bool {
    if let Err(_) = x {
        true
    } else {
        false
    }
}

#[pure]
#[requires="is_ok(x)"]
fn get_ok_bool(x: &Result<bool, UnexpectedValue>) -> bool {
    if let Ok(v) = x {
        *v
    } else {
        unreachable!()
    }
}

#[pure]
#[requires="is_ok(x)"]
fn get_ok_u32(x: &Result<u32, UnexpectedValue>) -> u32 {
    if let Ok(v) = x {
        *v
    } else {
        unreachable!()
    }
}

#[pure]
#[requires="is_err(x)"]
fn get_err_value<T: Copy>(x: &Result<T, UnexpectedValue>) -> u32 {
    if let Err(UnexpectedValue(v)) = x {
        *v
    } else {
        unreachable!()
    }
}

#[requires="0 <= i"]
#[ensures="i > 10 ==> (is_err(&result) && get_err_value(&result) == i)"]
#[ensures="is_err(&result) ==> get_err_value(&result) > 10"]
#[ensures="i <= 10 ==> is_ok(&result)"]
#[ensures="is_ok(&result) ==> i <= 10"]
#[ensures="!(i < 0 || 10 <= i) ==> !get_ok_bool(&result)"]
#[ensures="!(!is_ok(&result) || get_ok_bool(&result)) ==> (0 <= i && i < 10)"]
#[ensures="i == 10 ==> get_ok_bool(&result)"]
#[ensures="!(!is_ok(&result) || !get_ok_bool(&result)) ==> i == 10"]
fn done(i: u32) -> Result<bool, UnexpectedValue> {
    if 0 <= i && i <= 10 {
        Ok(i == 10)
    } else {
        let res = Err(UnexpectedValue(i));
        assert!(get_err_value(&res) > 10);
        res
    }
}

/// We don't yet support the "?" Rust operator, because it uses the following calls:
/// * std::ops::Try::from_error(..)
/// * std::ops::Try::into_result(..)
/// So, here is an alternative:
macro_rules! simple_try {
    ($e:expr) => {
        match $e {
            Err(err_val) => return Err(err_val),
            Ok(ok_val) => ok_val,
        }
    };
}

#[requires="0 <= start"]
#[ensures="is_ok(&result) ==> get_ok_u32(&result) == 10"]
#[ensures="is_err(&result) ==> (get_err_value(&result) == start && start > 10)"]
fn test_result_in_guard(start: u32) -> Result<u32, UnexpectedValue> {
    let mut i = start;

    #[invariant="0 <= i && i < 10"]
    while simple_try!(done(i)) == false {
        // Position of the invariant
        i += 1;
    }

    assert!(i == 10);
    Ok(i)
}

fn main() {}
