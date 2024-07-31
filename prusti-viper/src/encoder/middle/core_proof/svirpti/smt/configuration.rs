use prusti_common::config;
use rsmt2::SmtConf;

pub struct Configuration {
    pub(super) smt_conf: SmtConf,
    /// Attributes fed into solver's `set_info` method.
    pub(super) attributes: Vec<String>,
    /// Options fed into solver's `set_option` method.
    pub(super) options: Vec<(String, String)>,
    pub(super) tee_path: Option<String>,
}

impl Default for Configuration {
    fn default() -> Self {
        let mut smt_conf = SmtConf::z3(config::svirpti_smt_solver());
        smt_conf.check_success();
        let attributes = vec![(":smt-lib-version 2.0")]
            .into_iter()
            .map(|attribute| (attribute.into()))
            .collect();
        let options = vec![
            // Silicon.
            (":global-decls".to_string(), "true".to_string()),
            (":auto_config".to_string(), "false".to_string()),
            (":smt.case_split".to_string(), "3".to_string()),
            (":smt.delay_units".to_string(), "true".to_string()),
            (":type_check".to_string(), "true".to_string()),
            (":smt.mbqi".to_string(), "false".to_string()),
            (":pp.bv_literals".to_string(), "false".to_string()),
            (":smt.arith.solver".to_string(), "2".to_string()),
            (":model.v2".to_string(), "true".to_string()),
            (":smt.qi.max_multi_patterns".to_string(), "1000".to_string()),
            // (":timeout".to_string(), "5000".to_string()),
            // Prusti.
            (
                ":smt.qi.eager_threshold".to_string(),
                config::smt_qi_eager_threshold().to_string(),
            ),
            (
                ":model.partial".to_string(),
                config::counterexample().to_string(),
            ),
            (
                ":smt.arith.nl".to_string(),
                config::smt_use_nonlinear_arithmetic_solver().to_string(),
            ),
            // (":smt.arith.nl.gb".to_string(), config::smt_use_nonlinear_arithmetic_solver().to_string()),
        ];
        let tee_path = config::svirpti_smt_solver_log();
        Self {
            smt_conf,
            options,
            attributes,
            tee_path,
        }
    }
}
