pub enum SupportStatus {
    Supported,
    Unsupported(String)
}

impl SupportStatus {
    pub fn supported() -> Self {
        SupportStatus::Supported
    }
    pub fn unsupported(reason: String) -> Self {
        SupportStatus::Unsupported(reason)
    }

    #[allow(dead_code)]
    pub fn is_supported(&self) -> bool {
        match self {
            SupportStatus::Supported => true,
            SupportStatus::Unsupported(_) => false
        }
    }
}

#[macro_export]
macro_rules! requires {
    ($e:expr) => {
        match $e {
            SupportStatus::Unsupported(reason) => return SupportStatus::Unsupported(reason),
            SupportStatus::Supported => {}
        }
    };

    ($e:expr, $reason:expr) => {
        if !$e {
            return SupportStatus::Unsupported(
                format!($reason)
            );
        }
    };

    ($e:expr, $reason:expr, $($args:expr),*) => {
        if !$e {
            return SupportStatus::Unsupported(
                format!($reason, $($args:expr),*)
            );
        }
    };
}

#[macro_export]
macro_rules! unsupported {
    ($reason:expr) => {
        return SupportStatus::unsupported(
            format!($reason)
        );
    };

    ($reason:expr, $($args:expr),*) => {
        return SupportStatus::unsupported(
            format!($reason, $($args:expr),*)
        );
    };
}
