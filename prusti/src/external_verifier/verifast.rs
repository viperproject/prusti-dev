use prusti_interface::specs::{ExternFunctionName, ExternSpecification, TranslatedSpecMap};
use prusti_rustc_interface::data_structures::fx::FxHashMap;
use std::{
    fs::File,
    io::{self, Read, Write},
    iter::{Enumerate, Peekable},
    str::Chars,
};

pub enum ExternalVerificationError {
    IoError(std::io::Error, String),
    AmbiguousExternFunctionName(ExternFunctionName),
    FunctionNotFound(ExternFunctionName),
}

pub fn verify_external(translated_specs: TranslatedSpecMap) -> Vec<ExternalVerificationError> {
    translated_specs
        .into_iter()
        .filter(|(file, _)| file.ends_with(".c"))
        .flat_map(|(file, specs)| verify_external_c_file(&file, specs))
        .collect()
}

fn verify_external_c_file(
    file: &str,
    specs: FxHashMap<ExternFunctionName, ExternSpecification>,
) -> Vec<ExternalVerificationError> {
    let mut c_file_content = match read_external_c_file(file) {
        Ok(chars) => chars,
        Err(e) => return vec![ExternalVerificationError::IoError(e, file.to_owned())],
    };

    let errors = process_c_file(&mut c_file_content, &specs);
    if !errors.is_empty() {
        return errors;
    }

    match write_external_c_file(file, &c_file_content) {
        Ok(_) => vec![],
        Err(e) => vec![ExternalVerificationError::IoError(e, file.to_owned())],
    }
}

fn read_external_c_file(file: &str) -> io::Result<String> {
    let mut file = File::open(file)?;
    let mut chars = String::new();
    file.read_to_string(&mut chars)?;
    Ok(chars)
}

fn write_external_c_file(file: &str, c_code: &str) -> io::Result<()> {
    File::create(file)?.write_all(c_code.as_bytes())
}

fn process_c_file(
    c_code: &mut String,
    specs: &FxHashMap<ExternFunctionName, ExternSpecification>,
) -> Vec<ExternalVerificationError> {
    specs
        .iter()
        .map(|(function_name, specification)| {
            insert_specification(c_code, function_name, specification)
        })
        .flat_map(Result::err)
        .collect()
}

fn insert_specification(
    c_code: &mut String,
    function_name: &ExternFunctionName,
    spec: &ExternSpecification,
) -> Result<(), ExternalVerificationError> {
    let function_index = find_function(c_code, function_name)?;
    let parameter_list_length = skip_over_c_parameter_list(&c_code[function_index..]);
    let mut verifast_comments = vec![];
    for (v_comments, c) in
        skip_over_c_comments(c_code[function_index + parameter_list_length..].chars())
    {
        verifast_comments.extend(v_comments);
        if c == '{' {
            break;
        }
    }

    let mut offset = 0;
    verifast_comments.iter().for_each(|(start, end)| {
        c_code.replace_range(
            function_index + parameter_list_length + start - offset
                ..=function_index + parameter_list_length + end - offset,
            "",
        );
        offset += end - start + 1;
    });

    c_code.insert_str(
        function_index + parameter_list_length,
        &format!("\n//@ requires {};\n//@ ensures {};", spec.0, spec.1),
    );

    Ok(())
}

fn find_function(
    c_code: &str,
    function_name: &ExternFunctionName,
) -> Result<usize, ExternalVerificationError> {
    let mut found_index = None;
    let mut search_index = 0;
    while let Some(match_index) = c_code[search_index..].find(function_name) {
        search_index = match_index + function_name.len();
        if is_c_identifier_char(c_code[..match_index].chars().rev().next())
            || is_c_identifier_char(c_code[(match_index + function_name.len())..].chars().next())
        {
            continue;
        }
        found_index = match found_index {
            Some(_) => {
                return Err(ExternalVerificationError::AmbiguousExternFunctionName(
                    function_name.clone(),
                ))
            }
            None => Some(match_index),
        };
    }

    found_index.ok_or_else(|| ExternalVerificationError::FunctionNotFound(function_name.clone()))
}

fn is_c_identifier_char(c: Option<char>) -> bool {
    matches!(c, Some(c) if c.is_ascii_alphanumeric() || c == '_')
}

fn skip_over_c_parameter_list(c_code: &str) -> usize {
    let mut index = 0;
    let mut parenthesis_count = 0;

    for (_, c) in skip_over_c_comments(c_code.chars()) {
        index += 1;
        if c == '(' {
            parenthesis_count += 1;
        } else if c == ')' {
            parenthesis_count -= 1;
            if parenthesis_count == 0 {
                break;
            }
        }
    }

    return index;
}

fn skip_over_c_comments<'a>(
    chars: Chars<'a>,
) -> impl Iterator<Item = (Vec<(usize, usize)>, char)> + 'a {
    struct Iter<'a> {
        chars: Peekable<Enumerate<Chars<'a>>>,
    }

    impl<'a> Iterator for Iter<'a> {
        type Item = (Vec<(usize, usize)>, char);

        fn next(&mut self) -> Option<Self::Item> {
            let mut verifast_comments = vec![];
            loop {
                let next_char = self.chars.next();
                match (next_char, self.chars.peek()) {
                    (Some((start_index, '/')), Some((_, '/'))) => {
                        self.chars.next();
                        let is_verifast_comment = matches!(self.chars.peek(), Some((_, '@')));
                        let end_line = self.chars.find(|x| matches!(x, (_, '\n')));
                        if is_verifast_comment && end_line.is_some() {
                            verifast_comments.push((start_index, end_line.unwrap().0));
                        }
                        continue;
                    }
                    (Some((start_index, '/')), Some((_, '*'))) => {
                        self.chars.next();
                        let is_verifast_comment = matches!(self.chars.peek(), Some((_, '@')));
                        let end_index = loop {
                            self.chars.find(|x| matches!(x, (_, '*')));
                            let end = self.chars.peek().map(|(end_index, c)| (*end_index, *c));
                            if matches!(end, None | Some((_, '/'))) {
                                self.chars.next();
                                break end.map(|(end_index, _)| end_index);
                            }
                        };
                        if is_verifast_comment && end_index.is_some() {
                            verifast_comments.push((start_index, end_index.unwrap()));
                        }
                        continue;
                    }
                    (other, _) => return other.map(|(_, c)| (verifast_comments, c)),
                }
            }
        }
    }

    Iter {
        chars: chars.enumerate().peekable(),
    }
}
