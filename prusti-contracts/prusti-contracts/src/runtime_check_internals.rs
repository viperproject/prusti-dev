use core::fmt::Write;

struct SimpleFormatter<'a>(&'a mut [u8], usize);

impl<'a> core::fmt::Write for SimpleFormatter<'a> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let dest_len = self.0.len();
        let copy_len = core::cmp::min(s.len(), dest_len);

        self.0[..copy_len].copy_from_slice(&s.as_bytes()[..copy_len]);
        self.1 = copy_len;

        if s.len() > dest_len {
            Err(core::fmt::Error)
        } else {
            Ok(())
        }
    }
}

pub fn num_to_str<T: core::fmt::Display>(n: T, buffer: &mut [u8]) -> &str {
    let mut formatter = SimpleFormatter(buffer, 0);
    write!(&mut formatter, "{}", n).expect("Failed to write number to buffer");
    let bytes_written = formatter.1;
    core::str::from_utf8(&buffer[..bytes_written]).unwrap()
}

// An internal function used for getting more precise error messages for runtime
// checks.
// Buffer manipulations because we cannot use std and don't wanna introduce
// new dependencies.
#[cfg(not(feature = "std"))]
pub fn check_expr(expr: bool, added_info: &str, buffer: &mut [u8], buffer_len: &mut usize) -> bool {
    if !expr {
        // buffer already has contents up until buffer_len
        let after_len = *buffer_len + added_info.len();
        buffer[*buffer_len..after_len].copy_from_slice(added_info.as_bytes());
        *buffer_len = after_len;
        false
    } else {
        true
    }
}

#[cfg(feature = "std")]
pub fn check_expr(expr: bool, added_info: &str, message: &mut std::string::String) -> bool {
    if !expr {
        message.push_str(added_info);
        false
    } else {
        true
    }
}
