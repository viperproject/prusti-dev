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
// pub fn num_to_str<T>(mut n: T, buffer: &mut [u8;64]) -> &str
// where
//     T: PartialEq
//         + PartialOrd
//         + core::ops::Rem<Output = T>
//         + core::ops::Div<Output = T>
//         + core::ops::Sub<Output = T>
//         + Copy,
// {
//     let length = 0;
//     if n == 0 {
//         return "0"
//     }
//     let mut is_negative = false;
//     if n < T::from(0) {
//         is_negative = true;
//         n = T::from(0)-n;
//     }
//     let mut index = 63;
//     while n > T::from(0) {
//         let remainder: T = n % T::from(10);
//         buffer[index] = b'0' + (remainder as u8);
//         n = n / T::from(10);
//         index -= 1;
//     }
//     if is_negative {
//         buffer[index] = b'-';
//     } else {
//         index += 1;
//     }
//     core::str::from_utf8(&buffer[index..]).unwrap()
// }
// An internal function used for getting more precise error messages for runtime
// checks.
// Buffer manipulations because we cannot use std and don't wanna introduce
// new dependencies.
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
