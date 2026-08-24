fn main() {
    let [min, max] = test(42, 17);
}

fn test<T>(a: T, b: T) -> [T; 2] {
    [a, b]
}
