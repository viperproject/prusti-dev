//! Source: `045_ansi_term` crate

/// A style is a collection of properties that can format a string
/// using ANSI escape codes.
#[derive(PartialEq, Clone, Copy)]
pub struct Style {

    /// Whether this style is bold.
    pub is_bold: bool,

    /// Whether this style is dimmed.
    pub is_dimmed: bool,

    /// Whether this style is italic.
    pub is_italic: bool,

    /// Whether this style is underlined.
    pub is_underline: bool,

    /// Whether this style is blinking.
    pub is_blink: bool,

    /// Whether this style has reverse colours.
    pub is_reverse: bool,

    /// Whether this style is hidden.
    pub is_hidden: bool,

    /// Whether this style is struckthrough.
    pub is_strikethrough: bool
}

impl Style {
    /// Creates a new Style with no differences.
    pub fn new() -> Style {
        Style {
            is_bold: false,
            is_dimmed: false,
            is_italic: false,
            is_underline: false,
            is_blink: false,
            is_reverse: false,
            is_hidden: false,
            is_strikethrough: false,
        }
    }

    /// Returns a `Style` with the bold property set.
    pub fn bold(&self) -> Style {
        Style { is_bold: true, .. *self }
    }

    /// Returns a `Style` with the dimmed property set.
    pub fn dimmed(&self) -> Style {
        Style { is_dimmed: true, .. *self }
    }

    /// Returns a `Style` with the italic property set.
    pub fn italic(&self) -> Style {
        Style { is_italic: true, .. *self }
    }

    /// Returns a `Style` with the underline property set.
    pub fn underline(&self) -> Style {
        Style { is_underline: true, .. *self }
    }

    /// Returns a `Style` with the blink property set.
    pub fn blink(&self) -> Style {
        Style { is_blink: true, .. *self }
    }

    /// Returns a `Style` with the reverse property set.
    pub fn reverse(&self) -> Style {
        Style { is_reverse: true, .. *self }
    }

    /// Returns a `Style` with the hidden property set.
    pub fn hidden(&self) -> Style {
        Style { is_hidden: true, .. *self }
    }

    /// Returns a `Style` with the hidden property set.
    pub fn strikethrough(&self) -> Style {
        Style { is_strikethrough: true, .. *self }
    }
}

impl Default for Style {

    /// Returns a style with *no* properties set. Formatting text using this
    /// style returns the exact same text.
    ///
    /// ```
    /// use ansi_term::Style;
    /// assert_eq!(None,  Style::default().foreground);
    /// assert_eq!(None,  Style::default().background);
    /// assert_eq!(false, Style::default().is_bold);
    /// assert_eq!("txt", Style::default().paint("txt").to_string());
    /// ```
    fn default() -> Style {
        Style {
            is_bold: false,
            is_dimmed: false,
            is_italic: false,
            is_underline: false,
            is_blink: false,
            is_reverse: false,
            is_hidden: false,
            is_strikethrough: false,
        }
    }
}

fn main() {}
