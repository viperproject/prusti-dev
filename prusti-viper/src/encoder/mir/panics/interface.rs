use crate::encoder::errors::{PanicCause, SpannedEncodingResult};
use log::debug;
use prusti_rustc_interface::span::Span;

pub(crate) trait MirPanicsEncoderInterface<'tcx> {
    fn encode_panic_cause(&self, span: Span) -> SpannedEncodingResult<PanicCause>;
}

impl<'v, 'tcx: 'v> MirPanicsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn encode_panic_cause(&self, span: Span) -> SpannedEncodingResult<PanicCause> {
        let macro_backtrace: Vec<_> = span.macro_backtrace().collect();
        debug!("macro_backtrace: {:?}", macro_backtrace);

        // To classify the cause of the panic it's enough to look at the top 3 macro calls
        let lookup_size = 3;
        let tcx = self.env().tcx();
        let macro_names: Vec<String> = macro_backtrace
            .iter()
            .take(lookup_size)
            .filter_map(|x| x.macro_def_id.map(|y| tcx.def_path_str(y)))
            .collect();
        debug!("macro_names: {:?}", macro_names);

        let macro_names_str: Vec<&str> = macro_names.iter().map(|x| x.as_str()).collect();
        let cause = match &macro_names_str[..] {
            ["core::panic::panic_2015", "core::macros::panic", "std::unimplemented"] => {
                PanicCause::Unimplemented
            }
            ["std::unimplemented", ..] => PanicCause::Unimplemented,
            ["core::panic::panic_2015", "core::macros::panic", "std::unreachable"] => {
                PanicCause::Unreachable
            }
            ["std::unreachable", ..] => PanicCause::Unreachable,
            ["std::assert", "std::debug_assert", ..] => PanicCause::DebugAssert,
            ["std::assert", ..] => PanicCause::Assert,
            ["std::panic::panic_2015", "std::panic", "std::debug_assert"] => {
                PanicCause::DebugAssert
            }
            // TODO: assert!(_, "") currently has the same backtrace as panic!()
            // see https://github.com/rust-lang/rust/issues/82157
            //["std::panic::panic_2015", "std::panic", ..] => PanicCause::Assert,
            ["std::panic::panic_2015", "std::panic", ..] => PanicCause::Panic,
            _ => PanicCause::Generic,
        };
        Ok(cause)
    }
}
