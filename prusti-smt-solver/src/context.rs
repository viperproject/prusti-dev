use async_std::{
    fs::File,
    io::{prelude::BufReadExt, BufReader, BufWriter, WriteExt},
    net::TcpStream,
    sync::Mutex,
};
use std::{env::VarError, str::FromStr};

#[derive(Debug)]
pub(super) struct Context {
    pub(crate) quantifier_instantiations_bound_global: Option<u64>,
    pub(crate) log_file: Option<Mutex<BufWriter<File>>>,
    pub(crate) z3_trace_path: Option<String>,
}

impl Context {
    pub(crate) async fn new() -> Self {
        let (log_file_path, z3_trace_path) =
            if let Some(port) = read_integer("PRUSTI_SMT_SOLVER_MANAGER_PORT") {
                let stream = TcpStream::connect(("127.0.0.1", port)).await.unwrap();
                let mut reader = BufReader::new(stream);
                let mut log_file_path = String::new();
                reader.read_line(&mut log_file_path).await.unwrap();
                log_file_path.pop();
                let mut z3_trace_path = String::new();
                reader.read_line(&mut z3_trace_path).await.unwrap();
                z3_trace_path.pop();
                (Some(log_file_path), Some(z3_trace_path))
            } else {
                (None, None)
            };
        let quantifier_instantiations_bound_global =
            read_integer("PRUSTI_SMT_QUANTIFIER_INSTANTIATIONS_BOUND_GLOBAL");
        let log_file = {
            if let Ok(value) = std::env::var("PRUSTI_LOG_SMT_INTERACTION") {
                if value == "true" {
                    let file = File::create(log_file_path.as_ref().unwrap()).await.unwrap();
                    Some(Mutex::new(BufWriter::new(file)))
                } else {
                    None
                }
            } else {
                None
            }
        };

        Self {
            quantifier_instantiations_bound_global,
            log_file,
            z3_trace_path,
        }
    }

    pub(crate) async fn write_to_log(
        &self,
        stream: &str,
        line: &str,
    ) -> Result<(), std::io::Error> {
        if let Some(log_file) = &self.log_file {
            let mut file = log_file.lock().await;
            write!(file, "{}: {}", stream, line).await?;
        }
        Ok(())
    }

    pub(crate) async fn write_number_to_log(
        &self,
        stream: &str,
        number: u128,
    ) -> Result<(), std::io::Error> {
        if let Some(log_file) = &self.log_file {
            let mut file = log_file.lock().await;
            writeln!(file, "{}: {}", stream, number).await?;
        }
        Ok(())
    }

    pub(crate) async fn write_config_to_log(&self) -> Result<(), std::io::Error> {
        self.write_to_log("context", "--------\n-").await?;
        self.write_to_log("context", &format!("{:?}\n", self))
            .await?;
        self.write_to_log("context", "---------\n").await?;
        Ok(())
    }

    pub(crate) async fn check(&self, command: &str, response: &str) -> Result<(), std::io::Error> {
        if let Some(quantifier_instantiations_bound_global) =
            self.quantifier_instantiations_bound_global
        {
            if command == "(get-info :all-statistics)\n" {
                for line in response.lines() {
                    if line.starts_with(" :quant-instantiations") {
                        let mut words = line.split_whitespace();
                        words.next().unwrap();
                        let quant_instantiations: u64 = words.next().unwrap().parse().unwrap();
                        assert!(
                            quant_instantiations < quantifier_instantiations_bound_global,
                            "Quantifier instantiation bound exceeded: {} < {}",
                            quant_instantiations,
                            quantifier_instantiations_bound_global
                        );
                    }
                }
            }
        }
        Ok(())
    }
}

fn read_integer<T: FromStr>(name: &str) -> Option<T>
where
    <T as FromStr>::Err: std::fmt::Debug,
{
    match std::env::var(name) {
        Ok(value) => Some(value.parse().unwrap()),
        Err(VarError::NotPresent) => None,
        Err(_) => panic!("Invalid value of the environment variable"),
    }
}
