fn main() {
    let _ = vec![1]; //~ ERROR unsizing a std::boxed::Box<[i32; 1]> into a std::boxed::Box<[i32]> is not supported
}