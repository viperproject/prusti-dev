use std::env;

#[cfg(target_os = "linux")]
fn find_default_java_home() -> String {
    // TODO: How is this with non-Debian distributions?
    String::from("/usr/lib/jvm/default-java")
}

#[cfg(target_os = "macos")]
fn find_default_java_home() -> String {
    // TODO: Find paths dynamically, e.g. via `/usr/libexec/java_home -v 1.8`
    String::from(
        "/Library/Java/JavaVirtualMachines/jdk1.8.0_51.jdk/Contents/Home",
    )
}

#[cfg(target_os = "windows")]
fn find_default_java_home() -> String {
    // TODO: Find paths dynamically, especially regarding 32-bit/64-bit paths / `Program Files (x86)` / `Program Files`.
    String::from("C:\\Program Files\\Java\\jre8")
}

fn main() {
    // Try to determine the Java home directory so that we can link to `libjvm`.
    let java_home = env::var("JAVA_HOME").ok().unwrap_or(
        find_default_java_home(),
    );

    // TODO: Why is this necessary?
    print!("cargo:rustc-link-search=native=");
    println!("{}/jre/lib/server", java_home);

    if cfg!(target_arch = "x86_64") {
        print!("cargo:rustc-link-search=native=");
        println!("{}/jre/lib/amd64/server", java_home);
    } else if cfg!(target_arch = "x86") {
        print!("cargo:rustc-link-search=native=");
        println!("{}/jre/lib/i386/server", java_home);
    } else {
        panic!("rucaja is not currently supported on your architecture")
    }

    // TODO: handle something like `LD_LIBRARY_PATH` at runtime?
}
