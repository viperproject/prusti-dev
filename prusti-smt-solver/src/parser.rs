use crate::{
    error::{Error, ErrorKind},
    types::{Fingerprint, Id, TermId},
};
use std::str::CharIndices;

pub(crate) enum EventKind {
    Pop,
    Push,
    MkQuant,
    NewMatch,
    Unrecognized,
}

pub(crate) enum QuantTerm {
    Single(TermId),
    Pair(TermId, TermId),
}

pub(crate) struct Parser<'a> {
    line: &'a str,
    next: Option<(usize, char)>,
    cursor: CharIndices<'a>,
}

impl<'a> Parser<'a> {
    pub(crate) fn from_line(line: &'a str) -> Self {
        Self {
            line,
            next: None,
            cursor: line.char_indices(),
        }
    }

    fn error(&self, kind: ErrorKind) -> Error {
        Error {
            kind,
            line: self
                .next
                .clone()
                .into_iter()
                .chain(self.cursor.clone())
                .map(|(_, c)| c)
                .collect(),
        }
    }

    fn peek_with_position(&mut self) -> Option<(usize, char)> {
        if self.next.is_none() {
            self.next = self.cursor.next();
        }
        self.next
    }

    fn peek(&mut self) -> Option<char> {
        self.peek_with_position().map(|(_, c)| c)
    }

    fn advance_cursor(&mut self) {
        assert!(self.next.is_some());
        self.next = None;
    }

    fn position(&mut self) -> usize {
        self.peek_with_position().unwrap().0
    }

    fn try_consume_predicate(&mut self, predicate: impl Fn(char) -> bool) -> bool {
        if let Some(c) = self.peek() {
            if predicate(c) {
                self.advance_cursor();
                return true;
            }
        }
        false
    }

    fn consume_while_predicate<F>(&mut self, predicate: F) -> &str
    where
        F: Fn(char) -> bool,
        F: Copy,
    {
        let start = self.position();
        while self.try_consume_predicate(predicate) {}
        let end = self.position();
        &self.line[start..end]
    }

    pub(crate) fn try_consume(&mut self, arg: char) -> bool {
        self.try_consume_predicate(|c| c == arg)
        // if let Some(c) = self.peek() {
        //     if c == arg {
        //         self.advance_cursor();
        //         return true;
        //     }
        // }
        // false
    }

    pub(crate) fn consume(&mut self, arg: char) -> Result<(), Error> {
        if self.try_consume(arg) {
            Ok(())
        } else {
            Err(self.error(ErrorKind::ConsumeFailed))
        }
    }

    pub(crate) fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance_cursor();
            } else {
                break;
            }
        }
    }

    pub(crate) fn parse_event_kind(&mut self) -> Result<EventKind, Error> {
        if self.try_consume('[') {
            let kind = self.consume_while_predicate(|c| c.is_alphabetic() || c == '-');
            // let start = self.position();
            // while self.try_consume_predicate(|c| c.is_alphabetic() || c == '-') {}
            // let end = self.position();
            // let kind = match &self.line[start..end] {
            let kind = match kind {
                "pop" => EventKind::Pop,
                "push" => EventKind::Push,
                "mk-quant" => EventKind::MkQuant,
                "new-match" => EventKind::NewMatch,
                "tool-version" | "mk-app" | "attach-var-names" | "attach-meaning" | "mk-var"
                | "mk-proof" | "attach-enode" | "inst-discovered" | "instance"
                | "end-of-instance" | "mk-lambda" | "begin-check" | "assign" | "eq-expl"
                | "decide-and-or" | "resolve-lit" | "resolve-process" | "conflict" | "eof" => {
                    EventKind::Unrecognized
                }
                x => unimplemented!("got: {:?}", x),
            };
            self.consume(']')?;
            return Ok(kind);
        }
        Ok(EventKind::Unrecognized)
    }

    pub(crate) fn try_parse_id(&mut self) -> Result<Option<Id>, Error> {
        self.skip_whitespace();
        if self.try_consume('#') {
            Ok(Some(self.parse_number()?))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn parse_id(&mut self) -> Result<Id, Error> {
        if let Some(id) = self.try_parse_id()? {
            Ok(id)
        } else {
            Err(self.error(ErrorKind::ParseIdFailed))
        }
    }

    pub(crate) fn try_parse_quant_term(&mut self) -> Result<Option<QuantTerm>, Error> {
        self.skip_whitespace();
        let quant_term = if self.try_consume('(') {
            let original = self.parse_id()?;
            let matched = self.parse_id()?;
            self.consume(')')?;
            if original != matched {
                // An optimization.
                Some(QuantTerm::Pair(original, matched))
            } else {
                Some(QuantTerm::Single(matched))
            }
        } else {
            self.try_parse_id()?.map(QuantTerm::Single)
        };
        Ok(quant_term)
    }

    pub(crate) fn parse_name(&mut self) -> Result<String, Error> {
        self.skip_whitespace();
        fn is_valid_name(c: char) -> bool {
            c.is_alphanumeric() || "$.<>=!%@-[]_".contains(c)
        }
        // let start = self.position();
        // while self.try_consume_predicate(is_valid_name) {}
        // let end = self.position();
        Ok(self.consume_while_predicate(is_valid_name).to_string())
        // Ok(self.line[start..end].to_string())
    }

    pub(crate) fn check_eof(&mut self) -> Result<(), Error> {
        self.skip_whitespace();
        if self.peek().is_none() {
            Ok(())
        } else {
            Err(self.error(ErrorKind::EofCheckFailed))
        }
    }

    pub(crate) fn parse_hex_number(&mut self) -> Result<Fingerprint, Error> {
        self.skip_whitespace();
        self.consume('0')?;
        let mut number = 0;
        if self.try_consume('x') {
            // let start = self.position();
            // while self.try_consume_predicate(|c| c.is_ascii_hexdigit()) {}
            // let end = self.position();

            number =
                u64::from_str_radix(self.consume_while_predicate(|c| c.is_ascii_hexdigit()), 16)
                    .unwrap();
            // while let Some(c) = self.peek() {
            //     if c.is_ascii_hexdigit() {
            //         number *= 16;
            //         let value = u64::from_char_radix(c, 16).unwrap();
            //         // let value: u64 = match c {
            //         //     'a' => 10,
            //         //     'b' => 11,
            //         //     'c' => 12,
            //         //     'd' => 13,
            //         //     'e' => 14,
            //         //     'f' => 15,
            //         //     _ => c.try_into().unwrap(),
            //         // };
            //         number += value;
            //         eprintln!("hex: {} → {}", c, value);
            //         self.advance_cursor();
            //     } else {
            //         break;
            //     }
            // }
        }
        Ok(number)
    }

    pub(crate) fn parse_number(&mut self) -> Result<u32, Error> {
        self.skip_whitespace();
        let number =
            u32::from_str_radix(self.consume_while_predicate(|c| c.is_ascii_hexdigit()), 10)
                .unwrap();
        // let mut number = 0;
        // while let Some(c) = self.peek() {
        //     if c.is_numeric() {
        //         number *= 10;
        //         let value: u32 = c.try_into().unwrap();
        //         number += value;
        //         self.advance_cursor();
        //     } else {
        //         break;
        //     }
        // }
        Ok(number)
    }
}
