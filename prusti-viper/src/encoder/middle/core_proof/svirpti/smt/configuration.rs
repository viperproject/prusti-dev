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
        let smt_conf = SmtConf::z3(config::svirpti_smt_solver());
        let attributes = vec![(":smt-lib-version 2.0")]
            .into_iter()
            .map(|attribute| (attribute.into()))
            .collect();
        let options = vec![
            (":AUTO_CONFIG", "false"),
            (":smt.MBQI", "false"),
            (":TYPE_CHECK", "true"),
        ]
        .into_iter()
        .map(|(option, value)| (option.into(), value.into()))
        .collect();
        let tee_path = config::svirpti_smt_solver_log();
        Self {
            smt_conf,
            options,
            attributes,
            tee_path,
        }
    }
}
