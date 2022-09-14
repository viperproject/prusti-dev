use std::fmt::{Display, Write};

pub macro condition($condition: expr, $then_template: expr, $else_template: expr) {{
    if $condition {
        $then_template
    } else {
        $else_template
    }
}}

pub macro option($option: expr, $some_template: expr, $none_template: expr) {{
    match $option {
        Some(value) => format!($some_template, value),
        None => $none_template.to_string(),
    }
}}

pub(crate) macro option_cjoin($option: expr, $none_template: expr) {{
    match $option {
        Some(value) => $crate::common::display::cjoin(value),
        None => $none_template.to_string(),
    }
}}

pub fn cjoin<T: Display>(values: &[T]) -> String {
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
        write!(buf, "{value}").unwrap();
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

pub(crate) macro foreach2($template: expr, $values1: expr, $values2: expr) {{
    let mut buf = String::new();
    for (value1, value2) in $values1.zip($values2) {
        write!(buf, $template, value1, value2)?;
    }
    buf
}}

pub(crate) macro option_foreach($option: expr, $some_template: expr, $each_template: expr, $none_template: expr) {{
    match $option {
        Some(value) => format!(
            $some_template,
            $crate::common::display::foreach!($each_template, value)
        ),
        None => $none_template.to_string(),
    }
}}
