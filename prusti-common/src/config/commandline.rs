use config_crate::{Value, Source, ConfigError};
use std::collections::HashMap;
use std::env;

#[derive(Clone, Debug)]
pub struct CommandLine {
    /// Optional prefix that will limit args to those that begin with the defined prefix.
    /// 
    /// Example: The arg -Zdebug=true would become debug=true with a prefix of -Z
    prefix: Option<String>,

    /// Character sequence that separates key, value pairs. The default separator is '=', 
    /// the separator pattern must only occur once in the flag or it will be ignored.
    /// 
    /// Example: debug=true is a valid key,val pair with separator of '='
    ///          debug= would be invalid because there is no value.
    ///          debug+true would be valid with a separator of '+' 
    separator: String,

    /// Boolean indicating whether invalid flags should be ignored or result in a ConfigError
    /// 
    /// Note: the method get_remaining_args always
    ///       returns the invalid args regardless of this boolean 
    ignore_invalid: bool,
}

impl CommandLine {
    pub fn new() -> Self {
        CommandLine::default()
    }

    pub fn with_prefix(s: &str) -> Self {
        CommandLine {
            prefix: Some(s.to_owned()),
            ..CommandLine::default()
        }
    }

    pub fn prefix(mut self, s: &str) -> Self {
        self.prefix = Some(s.into());
        self
    }

    pub fn separator(mut self, s: &str) -> Self {
        self.separator = s.into();
        self
    }

    pub fn ignore_invalid(mut self, ignore: bool) -> Self {
        self.ignore_invalid = ignore;
        self
    }

    /// Return String iterator of arguments that are invalid.
    pub fn get_remaining_args(self) -> impl Iterator<Item = String> {
        env::args()
            .filter(move |arg| !self.is_valid_arg(arg))
    }

    // An argument is valid if it begins with the optional
    // prefix, the separator pattern occurrs exactly once, 
    // and the separator separates two non-empty strings.
    fn is_valid_arg(&self, arg: &str) -> bool {
        let prefix = self.get_prefix();
        if arg.starts_with(&prefix) {
            return arg[prefix.len()..].split(&self.separator)
                .map(|s| if s.is_empty() { 3 } else { 1 })
                .sum::<i32>() == 2;
        }
        false
    }

    fn get_prefix(&self) -> String {
        match self.prefix {
            Some(ref prefix) => prefix.to_owned(),
            _ => String::default(),
        }
    }
}

impl Default for CommandLine {
    fn default() -> CommandLine {
        CommandLine {
            prefix: None,
            separator: String::from("="),
            ignore_invalid: false,
        }
    }
}

impl Source for CommandLine {
    fn clone_into_box(&self) -> Box<dyn Source + Send + Sync> {
        Box::new((*self).clone())
    }

    fn collect(&self) -> Result<HashMap<String, Value>, ConfigError> {
        let mut m = HashMap::new();
        let uri = String::from("command-line");

        let prefix_pattern = self.get_prefix();

        for arg in env::args() {

            if !self.is_valid_arg(&arg) {
                if !self.ignore_invalid {
                    return Err(ConfigError::Message(format!("Invalid commandline arg: '{}'", arg)));
                }

                continue;
            } 

            let parts: Vec<&str> = arg.split(&self.separator).collect();

            let key = parts[0][prefix_pattern.len()..].to_lowercase().to_owned();
            let val = parts[1].to_owned();

            m.insert(
                key,
                Value::new(Some(&uri), val),
            );
        } 

        Ok(m)
    }
}