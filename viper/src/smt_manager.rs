use futures::FutureExt;
use std::{
    path::PathBuf,
    thread::{self, JoinHandle},
};
use tokio::{io::AsyncWriteExt, net::TcpListener, runtime::Builder, sync::oneshot};

#[derive(Default)]
pub struct SmtManager {
    connection: Option<Connection>,
    preserve_trace_files: bool,
    write_smt_statistics: bool,
    quantifier_instantiations_ignore_builtin: bool,
    quantifier_instantiations_bound_global_kind: Option<u64>,
    quantifier_instantiations_bound_trace: Option<u64>,
    quantifier_instantiations_bound_trace_kind: Option<u64>,
    unique_triggers_bound: Option<u64>,
    unique_triggers_bound_total: Option<u64>,
}

struct Connection {
    smt_listener: JoinHandle<Vec<String>>,
    termination_shot: oneshot::Sender<()>,
    port: u16,
}

impl SmtManager {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        log_path: PathBuf,
        preserve_trace_files: bool,
        write_smt_statistics: bool,
        quantifier_instantiations_ignore_builtin: bool,
        quantifier_instantiations_bound_global_kind: Option<u64>,
        quantifier_instantiations_bound_trace: Option<u64>,
        quantifier_instantiations_bound_trace_kind: Option<u64>,
        unique_triggers_bound: Option<u64>,
        unique_triggers_bound_total: Option<u64>,
    ) -> Self {
        let log_path = std::fs::canonicalize(log_path).unwrap();
        let (termination_sender, termination_receiver) = oneshot::channel();
        let (port_sender, port_receiver) = std::sync::mpsc::channel();
        let smt_listener = thread::spawn(move || {
            let runtime = Builder::new_current_thread()
                .thread_name("prusti-smt-manager")
                .enable_all()
                .build()
                .expect("failed to construct Tokio runtime");
            runtime.block_on(async {
                let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
                let address = listener.local_addr().unwrap();
                port_sender.send(address.port()).unwrap();

                let mut termination_receiver = termination_receiver.fuse();

                let mut counter = 0;
                let mut trace_files = Vec::new();

                loop {
                    let accept = listener.accept().fuse();
                    futures::pin_mut!(accept);
                    futures::select! {
                        value = termination_receiver => {
                            value.unwrap();
                            break;
                        }
                        socket = accept => {
                            let (mut socket, _) = socket.unwrap();
                            let log_file = log_path.join(format!("wrapper_{counter}.log"));
                            let trace_file = log_path.join(format!("trace{counter}.log"));
                            let log_file = log_file.into_os_string().into_string().unwrap();
                            let trace_file = trace_file.into_os_string().into_string().unwrap();
                            socket.write_all(log_file.as_bytes()).await.unwrap();
                            socket.write_all(b"\n").await.unwrap();
                            socket.write_all(trace_file.as_bytes()).await.unwrap();
                            socket.write_all(b"\n").await.unwrap();
                            trace_files.push(trace_file);
                            socket.flush().await.unwrap();
                            socket.shutdown().await.unwrap();
                            counter += 1;
                        }
                    }
                }
                trace_files
            })
        });
        let connection = Connection {
            smt_listener,
            termination_shot: termination_sender,
            port: port_receiver.recv().unwrap(),
        };
        Self {
            connection: Some(connection),
            preserve_trace_files,
            write_smt_statistics,
            quantifier_instantiations_ignore_builtin,
            quantifier_instantiations_bound_global_kind,
            quantifier_instantiations_bound_trace,
            quantifier_instantiations_bound_trace_kind,
            unique_triggers_bound,
            unique_triggers_bound_total,
        }
    }

    pub fn port(&self) -> u16 {
        self.connection.as_ref().unwrap().port
    }

    pub fn stop_and_check(&mut self) {
        if let Some(connection) = self.connection.take() {
            connection.termination_shot.send(()).unwrap();
            let trace_files = connection.smt_listener.join().unwrap();
            for trace_file in trace_files {
                let trace_file = PathBuf::from(trace_file);
                // Since Silicon kills the SMT solver, there is no guarantee
                // that the scopes will be fully popped.
                let expected_scopes_count = None;
                let settings = smt_log_analyzer::Settings {
                    write_statistics: self.write_smt_statistics,
                    quantifier_instantiations_ignore_builtin: self
                        .quantifier_instantiations_ignore_builtin,
                    quantifier_instantiations_bound_global_kind: self
                        .quantifier_instantiations_bound_global_kind,
                    quantifier_instantiations_bound_trace: self
                        .quantifier_instantiations_bound_trace,
                    quantifier_instantiations_bound_trace_kind: self
                        .quantifier_instantiations_bound_trace_kind,
                    unique_triggers_bound: self.unique_triggers_bound,
                    unique_triggers_bound_total: self.unique_triggers_bound_total,
                    check_active_scopes_count: expected_scopes_count,
                    pop_scopes_by_one: false,
                    trace_quantifier_triggers: None,
                };
                smt_log_analyzer::analyze(&trace_file, settings).unwrap();
                if !self.preserve_trace_files {
                    std::fs::remove_file(trace_file).unwrap();
                }
            }
        }
    }
}

impl Drop for SmtManager {
    fn drop(&mut self) {
        assert!(self.connection.is_none(), "`stop_and_check` was not called");
    }
}
