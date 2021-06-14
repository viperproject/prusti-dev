fn main() {

    assert!(f64::NAN == f64::NAN);

    let x= (f64::NAN).is_nan();
    assert!(x);

}