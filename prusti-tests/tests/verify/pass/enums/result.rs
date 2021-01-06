use prusti_contracts::*;

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
#[requires(is_ok(x))]
fn get_ok_bool(x: &Result<bool, UnexpectedValue>) -> bool {
    if let Ok(v) = x {
        *v
    } else {
        unreachable!()
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
#[requires(is_ok(x))]
fn get_ok_u32(x: &Result<u32, UnexpectedValue>) -> u32 {
    if let Ok(v) = x {
        *v
    } else {
        unreachable!()
    }
}

#[pure]
#[requires(is_err(x))]
fn get_err_value<T: Copy>(x: &Result<T, UnexpectedValue>) -> u32 {
    if let Err(UnexpectedValue(v)) = x {
        *v
    } else {
        unreachable!()
    }
}


fn main() {}
