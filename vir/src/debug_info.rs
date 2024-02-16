use cfg_if::cfg_if;

// Imports
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        use crate::with_vcx;
        use std::{
            alloc::Layout,
            backtrace::Backtrace,
            ptr::NonNull
        };
    }
}

// Definition of `DebugInfo`
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        #[derive(Clone, Copy, Debug)]
        pub struct DebugInfo(Option<NonNull<DebugInfoData>>);

        impl PartialEq for DebugInfo {
            /// DebugInfo values are always be considered equal; this prevents
            /// breaking derived `PartialEq` implementations for types that contain
            /// DebugInfo values.
            fn eq(&self, _other: &Self) -> bool {
                true
            }
        }

        impl Eq for DebugInfo {}
    } else {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub struct DebugInfo;
    }
}

// DEBUGINFO_NONE
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(None);
    } else {
        pub const DEBUGINFO_NONE: DebugInfo = DebugInfo;
    }
}

// DebugInfoData
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        #[derive(Debug)]
        struct DebugInfoData {
            pub backtrace: Backtrace,
            pub debug_notes: Vec<String>
        }

        impl DebugInfoData {
            fn new() -> DebugInfoData {
                let backtrace = Backtrace::capture();
                DebugInfoData {
                    backtrace,
                    debug_notes: Vec::new()
                }
            }

            fn add_debug_note(&mut self, note: String) {
                self.debug_notes.push(note);
            }
        }

        impl std::fmt::Display for DebugInfoData {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "Debug Notes: {:?}", self.debug_notes)?;
                write!(f, "Backtrace: {}", self.backtrace)
            }
        }
    }
}

impl DebugInfo {
    // DebugInfo::new()
    cfg_if! {
        if #[cfg(feature="vir_debug")] {
            pub fn new() -> DebugInfo {
                let data = DebugInfoData::new();
                with_vcx(|vcx| {
                    let ptr = vcx.arena.alloc_layout(Layout::new::<DebugInfoData>());
                    let ptr = ptr.cast::<DebugInfoData>();
                    unsafe {
                        ptr.as_ptr().write(data);
                    }
                    DebugInfo(Some(ptr))
                })
            }
        } else {
            pub fn new() -> DebugInfo {
                DebugInfo
            }
        }
    }

    #[cfg(feature = "vir_debug")]
    pub fn add_debug_note_never_call_this_function_directly(&self, note: String) {
        unsafe {
            if let Some(ptr) = self.0 {
                let data = ptr.as_ptr().as_mut().unwrap();
                data.add_debug_note(note);
            } else {
                eprintln!(
                    "Attempted to add debug note, but the entity was not created with debug info"
                );
            }
        }
    }
}

impl std::fmt::Display for DebugInfo {
    // `Display` impl for DebugInfo
    cfg_if! {
        if #[cfg(feature="vir_debug")] {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self.0 {
                    Some(data) =>
                        unsafe {
                            write!(f, "{}", data.as_ref())
                        }
                    None => write!(f, "This entity was not created with debug info."),
                }
            }
        } else {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "No debug info available, recompile with --features=vir_debug")
            }
        }
    }
}

// add_debug_note! macro
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        #[macro_export]
        macro_rules! add_debug_note {
            ($debug_info:expr, $($arg:tt)*) => {{
                $debug_info.add_debug_note_never_call_this_function_directly(format!($($arg)*))
            }};
        }
    } else {
        #[macro_export]
        macro_rules! add_debug_note {
            ($debug_info:expr, $($arg:tt)*) => {{
                ()
            }};
        }
    }
}
