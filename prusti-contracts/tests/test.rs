#[test]
fn tests() {
    let runner = trybuild::TestCases::new();
    runner.pass("tests/pass/*.rs");
    runner.compile_fail("tests/fail/*.rs");
}
