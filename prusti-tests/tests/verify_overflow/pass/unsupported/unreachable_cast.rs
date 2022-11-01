// compile-flags: -Pallow_unreachable_unsupported_code=true

pub fn main() {
    if false {
        // Unsupported, but unreachable:
        let x = 0u32 as f32;
    } else {
        assert!(true);
    }
}
