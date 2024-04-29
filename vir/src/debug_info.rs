use cfg_if::cfg_if;
use crate::VirCtxt;

// Imports
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        use std::{
            backtrace::Backtrace,
            sync::Mutex,
        };
    } else {
        use std::marker::PhantomData;
    }
}

// Definition of `DebugInfo`
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        #[derive(Clone, Copy, Debug)]
        pub struct DebugInfo<'a>(Option<&'a Mutex<DebugInfoData>>);

        impl PartialEq for DebugInfo<'_> {
            /// DebugInfo values are always be considered equal; this prevents
            /// breaking derived `PartialEq` implementations for types that contain
            /// DebugInfo values.
            fn eq(&self, _other: &Self) -> bool {
                true
            }
        }

        impl Eq for DebugInfo<'_> {}
    } else {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub struct DebugInfo<'a>(PhantomData<&'a ()>);
    }
}

// serde and hash no-ops
impl serde::Serialize for DebugInfo<'_> {
    fn serialize<S>(&self, ser: S) -> Result<S::Ok, S::Error>
    where S: serde::ser::Serializer
    {
        ser.serialize_unit()
    }
}
impl<'de> serde::Deserialize<'de> for DebugInfo<'_> {
    fn deserialize<D>(deser: D) -> Result<Self, D::Error>
    where D: serde::de::Deserializer<'de>
    {
        deser.deserialize_unit(serde::de::IgnoredAny)?;
        Ok(DEBUGINFO_NONE)
    }
}
impl std::hash::Hash for DebugInfo<'_> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {}
}

// DEBUGINFO_NONE
cfg_if! {
    if #[cfg(feature="vir_debug")] {
        pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(None);
    } else {
        pub const DEBUGINFO_NONE: DebugInfo = DebugInfo(PhantomData);
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
                write!(f, "Debug Notes: {}", self.debug_notes.concat())?;
                write!(f, "Backtrace: {}", self.backtrace)
            }
        }
    }
}

impl <'vir> DebugInfo<'vir> {
    cfg_if! {
        if #[cfg(feature="vir_debug")] {
            pub fn new(vcx: &'vir VirCtxt<'_>) -> DebugInfo<'vir> {
                let debug_info_data = vcx.alloc(
                    Mutex::new(DebugInfoData::new())
                );
                DebugInfo(Some(debug_info_data))
            }
        } else {
            pub fn new(_vcx: &'vir VirCtxt<'_>) -> DebugInfo<'vir> {
                DebugInfo(PhantomData)
            }
        }
    }

    #[cfg(feature = "vir_debug")]
    pub fn add_debug_note_never_call_this_function_directly(&self, note: String) {
        if let Some(mutex) = self.0 {
            let mut data = mutex.lock().unwrap();
            data.add_debug_note(note);
        } else {
            eprintln!(
                "Attempted to add debug note, but the entity was not created with debug info"
            );
        }
    }
}

impl std::fmt::Display for DebugInfo<'_> {
    // `Display` impl for DebugInfo
    cfg_if! {
        if #[cfg(feature="vir_debug")] {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self.0 {
                    Some(data) => write!(f, "{}", data.lock().unwrap()),
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
