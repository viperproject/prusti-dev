use std::fmt::{Display, Write};

pub(crate) macro option($option: expr, $some_template: expr, $none_template: expr) {{
    match $option {
        Some(value) => format!($some_template, value),
        None => $none_template.to_string(),
    }
}}

pub(crate) fn cjoin<T: Display>(values: &[T]) -> String {
    join(", ", values)
}

pub(crate) fn join<T: Display>(separator: &str, values: &[T]) -> String {
    let mut buf = String::new();
    let mut first = true;
    for value in values {
        if first {
            first = false;
        } else {
            buf.push_str(separator);
        }
        write!(buf, "{}", value).unwrap();
    }
    buf
}

pub(crate) macro foreach($template: expr, $values: expr) {{
    let mut buf = String::new();
    for value in $values {
        write!(buf, $template, value)?;
    }
    buf
}}
