use prusti_rustc_interface::hir::def_id::DefId;
use prusti_rustc_interface::span::{source_map::SourceMap, Span};
use serde::Serialize;

use super::vsc_span::VscSpan;
/// stores the spans of a calls contracts. 
/// obtained during encoding

#[derive(Serialize, Clone)]
pub struct SpanOfCallContracts {
    pub defpath: String,
    pub call_span: VscSpan,
    pub contracts_spans: Vec<VscSpan>,    
}

impl SpanOfCallContracts {
    pub fn new(
        defpath: String, 
        call_span: Span, 
        contracts_spans: Vec<Span>, 
        source_map: &SourceMap
    ) -> Option<Self> {
        let call_span = VscSpan::from_span(&call_span, source_map)?;
        let contracts_spans = contracts_spans
            .iter()
            .filter_map(|sp| VscSpan::from_span(sp, source_map))
            .collect::<Vec<VscSpan>>();
        Some(Self {
            defpath,
            call_span,
            contracts_spans,
        })
    }

}

#[derive(Serialize)]
pub struct EncodingInfo {
    pub call_contract_spans: Vec<SpanOfCallContracts>,
}

impl EncodingInfo {
    pub fn to_json_string(self) -> String {
        serde_json::to_string(&self).unwrap()
    }
}

