use std::collections::HashSet;

#[derive(Clone, Eq, PartialEq, Hash)]
pub enum SupportKind {
    PartiallySupported(String),
    Unsupported(String)
}

impl SupportKind {
    pub fn partially(reason: String) -> Self {
        SupportKind::PartiallySupported(reason)
    }

    pub fn unsupported(reason: String) -> Self {
        SupportKind::Unsupported(reason)
    }

    pub fn is_partially_supported(&self) -> bool {
        match self {
            SupportKind::PartiallySupported(_) => true,
            _ => false
        }
    }

    pub fn is_unsupported(&self) -> bool {
        match self {
            SupportKind::Unsupported(_) => true,
            _ => false
        }
    }

    pub fn reason(&self) -> &str {
        match self {
            SupportKind::Unsupported(ref reason) |
            SupportKind::PartiallySupported(ref reason) => reason,
        }
    }
}


pub struct SupportStatus {
    restrictions: HashSet<SupportKind>
}

impl SupportStatus {
    pub fn new() -> Self {
        SupportStatus {
            restrictions: HashSet::new()
        }
    }

    pub fn partially(&mut self, reason: String) {
        self.restrictions.insert(
            SupportKind::partially(reason)
        );
    }

    #[allow(dead_code)]
    pub fn unsupported(&mut self, reason: String) {
        self.restrictions.insert(
            SupportKind::unsupported(reason)
        );
    }

    pub fn is_supported(&self) -> bool {
        self.restrictions.is_empty()
    }

    pub fn is_partially_supported(&self) -> bool {
        !self.restrictions.is_empty() &&
        self.restrictions.iter()
            .all(|s| s.is_partially_supported())
    }

    #[allow(dead_code)]
    pub fn is_unsupported(&self) -> bool {
        self.restrictions.iter()
            .any(|s| s.is_unsupported())
    }

    pub fn get_partially_supported_reasons(&self) -> Vec<String> {
        self.restrictions.iter()
            .filter(|s| s.is_partially_supported())
            .map(|s| s.reason().to_string())
            .collect()
    }

    #[allow(dead_code)]
    pub fn get_unsupported_reasons(&self) -> Vec<String> {
        self.restrictions.iter()
            .filter(|s| s.is_unsupported())
            .map(|s| s.reason().to_string())
            .collect()
    }
}

#[macro_export]
macro_rules! requires {
    ($self:expr, $e:expr, $reason:expr) => {
        if !$e {
            unsupported!($self, $reason);
        }
    };

    ($self:expr, $e:expr, $reason:expr, $($args:expr),*) => {
        if !$e {
            unsupported!($self, $reason, $($args:expr),*);
        }
    };
}

#[macro_export]
macro_rules! unsupported {
    ($self:expr, $reason:expr) => {
        $self.support.unsupported(
            format!($reason)
        );
    };

    ($self:expr, $reason:expr, $($args:expr),*) => {
        $self.support.unsupported(
            format!($reason, $($args:expr),*)
        );
    };
}

#[macro_export]
macro_rules! partially {
    ($self:expr, $reason:expr) => {
        $self.support.partially(
            format!($reason)
        );
    };

    ($self:expr, $reason:expr, $($args:expr),*) => {
        $self.support.partially(
            format!($reason, $($args:expr),*)
        );
    };
}
