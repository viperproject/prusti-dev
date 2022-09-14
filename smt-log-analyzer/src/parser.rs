use crate::{
    error::{Error, ErrorKind},
    types::{Fingerprint, Id, TermId},
};
use std::str::CharIndices;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) enum EventKind {
    Pop,
    Push,
    MkQuant,
    MkApp,
    NewMatch,
    InstDiscovered,
    Instance,
    Unrecognized,
    AttachMeaning,
    MkVar,
    ToolVersion,
    AttachVarNames,
    MkProof,
    AttachEnode,
    EndOfInstance,
    MkLambda,
    BeginCheck,
    Assign,
    EqExpl,
    DecideAndOr,
    ResolveLit,
    ResolveProcess,
    Conflict,
    Eof,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) enum TheoryKind {
    Arith,
    Basic,
    Datatype,
    UserSort,
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
            line: self.remaining(),
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

    pub(crate) fn remaining(&self) -> String {
        self.next
            .into_iter()
            .chain(self.cursor.clone())
            .map(|(_, c)| c)
            .filter(|c| *c != '\n')
            .collect()
    }

    pub(crate) fn try_consume(&mut self, arg: char) -> bool {
        self.try_consume_predicate(|c| c == arg)
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
            let kind = match kind {
                "pop" => EventKind::Pop,
                "push" => EventKind::Push,
                "mk-quant" => EventKind::MkQuant,
                "mk-app" => EventKind::MkApp,
                "mk-var" => EventKind::MkVar,
                "new-match" => EventKind::NewMatch,
                "inst-discovered" => EventKind::InstDiscovered,
                "instance" => EventKind::Instance,
                "attach-meaning" => EventKind::AttachMeaning,
                "tool-version" => EventKind::ToolVersion,
                "attach-var-names" => EventKind::AttachVarNames,
                "mk-proof" => EventKind::MkProof,
                "attach-enode" => EventKind::AttachEnode,
                "end-of-instance" => EventKind::EndOfInstance,
                "mk-lambda" => EventKind::MkLambda,
                "begin-check" => EventKind::BeginCheck,
                "assign" => EventKind::Assign,
                "eq-expl" => EventKind::EqExpl,
                "decide-and-or" => EventKind::DecideAndOr,
                "resolve-lit" => EventKind::ResolveLit,
                "resolve-process" => EventKind::ResolveProcess,
                "conflict" => EventKind::Conflict,
                "eof" => EventKind::Eof,
                x => unimplemented!("got: {:?}", x),
            };
            self.consume(']')?;
            return Ok(kind);
        }
        Ok(EventKind::Unrecognized)
    }

    pub(crate) fn parse_theory(&mut self) -> Result<TheoryKind, Error> {
        self.skip_whitespace();
        let kind = self.consume_while_predicate(|c| c.is_alphabetic() || c == '-');
        let kind = match kind {
            "basic" => TheoryKind::Basic,
            "arith" => TheoryKind::Arith,
            "datatype" => TheoryKind::Datatype,
            "user-sort" => TheoryKind::UserSort,
            _ => {
                eprintln!("kind: {kind:?}");
                eprintln!("self; {:?}", self.error(ErrorKind::ConsumeFailed));
                unimplemented!("got line: {:?}", self.line)
            }
        };
        self.consume('#')?;
        Ok(kind)
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

    pub(crate) fn parse_name(&mut self) -> Result<&str, Error> {
        self.skip_whitespace();
        fn is_valid_name(c: char) -> bool {
            c.is_alphanumeric() || "$.<>=!%@-[]_#".contains(c)
        }
        Ok(self.consume_while_predicate(is_valid_name))
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
            number =
                u64::from_str_radix(self.consume_while_predicate(|c| c.is_ascii_hexdigit()), 16)
                    .unwrap();
        }
        Ok(number)
    }

    pub(crate) fn parse_number(&mut self) -> Result<u32, Error> {
        self.skip_whitespace();
        let s = self.consume_while_predicate(|c| c.is_ascii_hexdigit());
        match s.parse() {
            Ok(number) => Ok(number),
            Err(error) => {
                eprintln!("error: {error}");
                eprintln!("string: {s}");
                eprintln!("line: {}", self.line);
                panic!();
            }
        }
    }
}
