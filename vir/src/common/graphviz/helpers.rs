pub fn escape_html<S: ToString>(s: S) -> String {
    s.to_string()
        .replace('&', "&amp;")
        .replace('>', "&gt;")
        .replace('<', "&lt;")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('|', "&#124;")
        .replace('\n', "<br/>")
}

pub fn escape_html_wrap<S: ToString>(s: S) -> String {
    substrings(&s.to_string(), 120)
        .into_iter()
        .map(escape_html)
        .collect::<Vec<_>>()
        .join(" \\ <br/>    ")
}

pub fn substrings(s: &str, max_length: usize) -> Vec<String> {
    let mut result = Vec::new();
    let mut start = 0;
    while start < s.len() {
        let end = std::cmp::min(start + max_length, s.len());
        result.push(s[start..end].to_string());
        start = end;
    }
    result
}
