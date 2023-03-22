fn main() {
    cc::Build::new()
        .file("src/clib.c")
        .compile("clib");
}
