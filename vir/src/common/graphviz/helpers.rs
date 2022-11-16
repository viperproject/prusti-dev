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
