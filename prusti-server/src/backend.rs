use crate::{dump_viper_program, ServerMessage};
use log::{debug, info};
use prusti_common::{
    config,
    vir::{LoweringContext, ToViper},
    Stopwatch,
};
use std::{
    sync::{mpsc, Arc},
    thread, time,
};
use viper::{jni_utils::JniUtils, VerificationContext, VerificationResultKind, Viper};
use viper_sys::wrappers::{java, viper::*};

pub enum Backend<'a> {
    Viper(
        viper::Verifier<'a>,
        &'a VerificationContext<'a>,
        &'a Arc<Viper>,
    ),
}

impl<'a> Backend<'a> {
    pub fn verify(
        &mut self,
        program: &prusti_common::vir::program::Program,
        sender: mpsc::Sender<ServerMessage>,
    ) -> VerificationResultKind {
        match self {
            Backend::Viper(ref mut verifier, context, viper_arc) => {
                let mut stopwatch =
                    Stopwatch::start("prusti-server backend", "construction of JVM objects");

                let ast_utils = context.new_ast_utils();

                ast_utils.with_local_frame(16, || {
                    let ast_factory = context.new_ast_factory();
                    let viper_program = program.to_viper(LoweringContext::default(), &ast_factory);

                    if config::dump_viper_program() {
                        stopwatch.start_next("dumping viper program");
                        dump_viper_program(
                            &ast_utils,
                            viper_program,
                            &program.get_name_with_check_mode(),
                        );
                    }

                    stopwatch.start_next("viper verification");
                    if config::report_viper_messages() {
                        verify_and_poll_msgs(verifier, context, viper_arc, viper_program, sender)
                    } else {
                        verifier.verify(viper_program)
                    }
                })
            }
        }
    }
}

fn verify_and_poll_msgs(
    verifier: &mut viper::Verifier,
    verification_context: &viper::VerificationContext,
    viper_arc: &Arc<Viper>,
    viper_program: viper::Program,
    sender: mpsc::Sender<ServerMessage>,
) -> VerificationResultKind {
    let mut kind = VerificationResultKind::Success;

    // get the reporter global reference outside of the thread scope because it needs to
    // be dropped by thread attached to the jvm. This is also why we pass it as reference
    // and not per value
    let env = &verification_context.env();
    let jni = JniUtils::new(env);
    let verifier_wrapper = silver::verifier::Verifier::with(env);
    let reporter = jni.unwrap_result(verifier_wrapper.call_reporter(*verifier.verifier_instance()));
    let rep_glob_ref = env.new_global_ref(reporter).unwrap();

    debug!("Starting viper message polling thread");

    // start thread for polling messages
    thread::scope(|scope| {
        let polling_thread = scope.spawn(|| polling_function(viper_arc, &rep_glob_ref, sender));
        kind = verifier.verify(viper_program);
        polling_thread.join().unwrap();
    });
    debug!("Viper message polling thread terminated");
    kind
}

fn polling_function(
    viper_arc: &Arc<Viper>,
    rep_glob_ref: &jni::objects::GlobalRef,
    sender: mpsc::Sender<ServerMessage>,
) {
    let verification_context = viper_arc.attach_current_thread();
    let env = verification_context.env();
    let jni = JniUtils::new(env);
    let reporter_instance = rep_glob_ref.as_obj();
    let reporter_wrapper = silver::reporter::PollingReporter::with(env);
    loop {
        while reporter_wrapper
            .call_hasNewMessage(reporter_instance)
            .unwrap()
        {
            let msg = reporter_wrapper
                .call_getNewMessage(reporter_instance)
                .unwrap();
            debug!("Polling thread received {}", jni.class_name(msg).as_str());
            match jni.class_name(msg).as_str() {
                "viper.silver.reporter.QuantifierInstantiationsMessage" => {
                    let msg_wrapper = silver::reporter::QuantifierInstantiationsMessage::with(env);
                    let q_name =
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_quantifier(msg)));
                    let q_inst = jni.unwrap_result(msg_wrapper.call_instantiations(msg));
                    debug!("QuantifierInstantiationsMessage: {} {}", q_name, q_inst);
                    // also matches the "-aux" and "_precondition" quantifiers generated
                    // we encoded the position id in the line and column number since this is not used by
                    // prusti either way
                    if q_name.starts_with("prog.l") {
                        let no_pref = q_name.strip_prefix("prog.l").unwrap();
                        let stripped = no_pref
                            .strip_suffix("-aux")
                            .or(no_pref.strip_suffix("_precondition"))
                            .unwrap_or(no_pref);
                        let parsed = stripped.parse::<u64>();
                        match parsed {
                            Ok(pos_id) => {
                                sender
                                    .send(ServerMessage::QuantifierInstantiation {
                                        q_name,
                                        insts: u64::try_from(q_inst).unwrap(),
                                        pos_id,
                                    })
                                    .unwrap();
                            }
                            _ => info!("Unexpected quantifier name {}", q_name),
                        }
                    }
                }
                "viper.silver.reporter.QuantifierChosenTriggersMessage" => {
                    let obj_wrapper = java::lang::Object::with(env);
                    let positioned_wrapper = silver::ast::Positioned::with(env);
                    let msg_wrapper = silver::reporter::QuantifierChosenTriggersMessage::with(env);

                    let viper_quant = jni.unwrap_result(msg_wrapper.call_quantifier(msg));
                    let viper_quant_str =
                        jni.get_string(jni.unwrap_result(obj_wrapper.call_toString(viper_quant)));
                    // we encoded the position id in the line and column number since this is not used by
                    // prusti either way
                    let pos = jni.unwrap_result(positioned_wrapper.call_pos(viper_quant));
                    let pos_string =
                        jni.get_string(jni.unwrap_result(obj_wrapper.call_toString(pos)));
                    let pos_id_index = pos_string.rfind('.').unwrap();
                    let pos_id = pos_string[pos_id_index + 1..].parse::<u64>().unwrap();

                    let viper_triggers =
                        jni.get_string(jni.unwrap_result(msg_wrapper.call_triggers__string(msg)));
                    debug!(
                        "QuantifierChosenTriggersMessage: {} {} {}",
                        viper_quant_str, viper_triggers, pos_id
                    );
                    sender
                        .send(ServerMessage::QuantifierChosenTriggers {
                            viper_quant: viper_quant_str,
                            triggers: viper_triggers,
                            pos_id,
                        })
                        .unwrap();
                }
                "viper.silver.reporter.VerificationTerminationMessage" => return,
                _ => (),
            }
        }
        thread::sleep(time::Duration::from_millis(10));
    }
}
