fn test() {
    let mut k: usize = 0;
    while k - 123 > 0 { } //~ ERROR attempt to subtract with overflow
}

fn main() {}
