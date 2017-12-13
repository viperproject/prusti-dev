#[allow(unused_macros)]
macro_rules! string_vec {
    ($($x:expr),*) => (vec![$($x.to_string()),*]);
}
