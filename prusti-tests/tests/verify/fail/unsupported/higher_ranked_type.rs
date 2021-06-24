fn main() {
    let _ = (0..1).filter(|_| true); //~ ERROR higher-ranked lifetimes and types are not supported
}