extern crate prusti_contracts;

pub enum MyOption<T> {
    Some(T),
    None
}

#[pure]
pub fn my_is_none<T>(s: &MyOption<T>) -> bool {
    match s {
        MyOption::Some(_) => false,
        MyOption::None => true,
    }
}

pub fn my_test1<T>(opt: MyOption<T>) {
    let _x = my_is_none(&opt);
}

pub fn my_test2<T>(value: T) {
    let opt = MyOption::Some(value);
    assert!(!my_is_none(&opt));
}

pub fn my_test3<T>() -> MyOption<T> {
    let opt = MyOption::None;
    assert!(my_is_none(&opt));
    opt
}

#[pure]
pub fn is_none<T>(s: &Option<T>) -> bool {
    match s {
        Some(_) => false,
        None => true,
    }
}

pub fn test1<T>(opt: Option<T>) {
    let _x = is_none(&opt);
}

pub fn test2<T>(value: T) {
    let opt = Some(value);
    assert!(!is_none(&opt));
}

pub fn test3<T>() -> Option<T> {
    let opt = None;
    assert!(is_none(&opt));
    opt
}

fn main() {
}
