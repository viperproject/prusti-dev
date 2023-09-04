use prusti_contracts::*;

fn main() {}

// split into many functions to avoid exponential branching complexity

fn test_1() {
    let ok = Result::<i32, String>::Ok(42);
    let err = Result::<i32, String>::Err("test".to_string());

    assert!(ok.is_ok());
    assert!(!ok.is_err());
    assert!(!err.is_ok());
    assert!(err.is_err());

    let some = Some(42);
    let none = Option::<i32>::None;
    assert!(ok.clone().ok() == some);
    assert!(err.clone().ok() == none);

    assert!(ok.as_ref().is_ok());
    assert!(err.as_ref().is_err());
}

fn test_2() {
    let ok = Result::<i32, bool>::Ok(42);
    let err = Result::<i32, bool>::Err(false);

    assert!(ok.map(|x| x + 1).is_ok());
    let _ = ok.map_or(69, |x| x + 1);
    assert!(err.map_or(69, |x| x + 1) == 69);
    let _ = ok.map_or_else(|_| 42, |x| x + 1);
    assert!(ok.map_err(|x| !x) == ok);
    assert!(err.map_err(|x| !x).is_err());
}

fn test_3() {
    let ok = Result::<i32, bool>::Ok(42);
    let err = Result::<i32, bool>::Err(false);

    assert!(ok.expect("test") == 42);
    assert!(ok.unwrap() == 42);
    assert!(ok.unwrap_or_default() == 42);
    //assert!(err.unwrap_or_default() == 0);
    assert!(err.expect_err("test") == false);
    assert!(err.unwrap_err() == false);
}

fn test_4() {
    let ok = Result::<i32, bool>::Ok(42);
    let ok2 = Result::<i32, bool>::Ok(5);
    let err = Result::<i32, bool>::Err(false);
    let err2 = Result::<i32, bool>::Err(true);

    assert!(ok.and(err2) == err2);
    assert!(ok.and(ok2) == ok2);
    assert!(err.and(ok2) == err);
    assert!(err.and(err2) == err);

    let _ = ok.and_then(|v| Result::<i32, bool>::Ok(v + 1));
    let _ = ok.and_then(|_| Result::<i32, bool>::Err(true));
    assert!(err.and_then(|v| Result::<i32, bool>::Ok(v + 1)) == err);
    assert!(err.and_then(|_| Result::<i32, bool>::Err(true)) == err);

    assert!(ok.or(err2) == ok);
    assert!(ok.or(ok2) == ok);
    assert!(err.or(ok2) == ok2);
    assert!(err.or(err2) == err2);

    assert!(ok.or_else(|_| Result::<i32, bool>::Ok(42)) == ok);
    assert!(ok.or_else(|e| Result::<i32, bool>::Err(e)) == ok);
    let _ = err.or_else(|_| Result::<i32, bool>::Ok(42));
    let _ = err.or_else(|e| Result::<i32, bool>::Err(e));
}

fn test_5() {
    let ok = Result::<i32, bool>::Ok(42);
    let err = Result::<i32, bool>::Err(false);

    assert!(ok.unwrap_or(69) == 42);
    assert!(err.unwrap_or(69) == 69);

    let _ = ok.unwrap_or_else(|_| 42);
    let _ = err.unwrap_or_else(|_| 42);

    assert!(ok.unwrap_or_default() == 42);
    assert!(err.unwrap_or_default() == 0);

    unsafe {
        assert!(ok.unwrap_unchecked() == 42);
        assert!(err.unwrap_err_unchecked() == false);
    }
}

fn test_transpose() {
    #[derive(Debug, Eq, PartialEq)]
    struct SomeErr;

    let x: Result<Option<i32>, SomeErr> = Ok(Some(5));
    let y: Option<Result<i32, SomeErr>> = Some(Ok(5));
    let x = x.transpose();
    prusti_assert!(x === y);
}
