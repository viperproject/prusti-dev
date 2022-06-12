use std::env::VarError;

use async_std::{
    fs::File,
    io::{prelude::BufReadExt, BufReader, WriteExt},
    path::PathBuf,
    process::{ChildStderr, ChildStdin, ChildStdout, Command, Stdio},
    sync::Mutex,
};
use futures::try_join;
use uuid::Uuid;

type LogFile = Mutex<File>;

fn are_parens_balanced(line: &str) -> bool {
    let openning_parens = line.chars().filter(|c| *c == '(').count();
    let closing_parens = line.chars().filter(|c| *c == ')').count();
    openning_parens == closing_parens
}

async fn write_to_log(log_file: &LogFile, stream: &str, line: &str) -> Result<(), std::io::Error> {
    let mut file = log_file.lock().await;
    write!(file, "{}: {}", stream, line).await.unwrap();
    Ok(())
}

async fn read_command(command: &mut String) -> Result<bool, std::io::Error> {
    command.clear();
    let stdin = async_std::io::stdin();
    while stdin.read_line(command).await? > 0 {
        if are_parens_balanced(command) {
            return Ok(true);
        }
    }
    Ok(false)
}

async fn read_response(
    solver_stdout: &mut BufReader<ChildStdout>,
    response: &mut String,
) -> Result<bool, std::io::Error> {
    response.clear();
    while solver_stdout.read_line(response).await? > 0 {
        if are_parens_balanced(response) {
            return Ok(true);
        }
    }
    Ok(false)
}

#[derive(Debug)]
struct Settings {
    quant_instantiations_bound: Option<u64>,
}

impl Settings {
    fn new() -> Self {
        let quant_instantiations_bound =
            match std::env::var("PRUSTI_SMT_QUANT_INSTANTIATIONS_BOUND") {
                Ok(value) => Some(value.parse().unwrap()),
                Err(VarError::NotPresent) => None,
                Err(_) => panic!("Invalid value of the environment variable"),
            };
        Self {
            quant_instantiations_bound,
        }
    }
}

async fn check(
    _log_file: &LogFile,
    command: &str,
    response: &str,
    settings: &Settings,
) -> Result<(), std::io::Error> {
    match command {
        "(get-info :all-statistics)\n" => {
            for line in response.lines() {
                if line.starts_with(" :quant-instantiations") {
                    let mut words = line.split_whitespace();
                    words.next().unwrap();
                    let quant_instantiations: u64 = words.next().unwrap().parse().unwrap();
                    if let Some(bound) = settings.quant_instantiations_bound {
                        assert!(
                            quant_instantiations < bound,
                            "Quantifier instantiation bound exceeded: {} < {}",
                            quant_instantiations,
                            bound
                        );
                    }
                }
            }
        }
        _ => {}
    }
    Ok(())
}

async fn communicate(
    log_file: &LogFile,
    mut solver_stdin: ChildStdin,
    solver_stdout: ChildStdout,
    settings: &Settings,
) -> Result<(), std::io::Error> {
    let mut stdout = async_std::io::stdout();
    let mut solver_stdout = BufReader::new(solver_stdout);
    let mut response = String::new();
    let mut command = String::new();
    while read_command(&mut command).await? {
        write_to_log(log_file, "in ", &command).await?;
        solver_stdin.write_all(command.as_bytes()).await?;
        solver_stdin.flush().await?;

        assert!(
            read_response(&mut solver_stdout, &mut response)
                .await
                .unwrap(),
            "reached EOF while reading response"
        );
        write_to_log(log_file, "out", &response).await?;
        stdout.write_all(response.as_bytes()).await?;
        stdout.flush().await?;

        check(log_file, &command, &response, settings).await?;
    }

    Ok(())
}

async fn pass_error(log_file: &LogFile, solver_stderr: ChildStderr) -> Result<(), std::io::Error> {
    let mut solver_stderr = BufReader::new(solver_stderr);
    let mut stderr = async_std::io::stderr();
    let mut line = String::new();
    {
        let mut file = log_file.lock().await;
        writeln!(file, "stderr started").await.unwrap();
    }
    while solver_stderr.read_line(&mut line).await? > 0 {
        {
            let mut file = log_file.lock().await;
            write!(file, "err: {}", line).await.unwrap();
        }
        stderr.write_all(line.as_bytes()).await?;
        stderr.flush().await?;
        line.clear();
    }
    {
        let mut file = log_file.lock().await;
        writeln!(file, "stderr finished").await.unwrap();
    }
    Ok(())
}

#[async_std::main]
async fn main() -> Result<(), std::io::Error> {
    let z3_path = std::env::var("PRUSTI_ORIGINAL_Z3_EXE").unwrap();
    // The directory at which the results are stored.
    let mut log_dir: PathBuf = std::env::var("PRUSTI_LOG_SMT").unwrap().into();
    let uuid = Uuid::new_v4().simple();
    let settings = Settings::new();
    log_dir.push(uuid.to_string());
    async_std::fs::create_dir_all(&log_dir).await?;
    let mut log_file_path = log_dir;
    log_file_path.push("log");
    let mut file = File::create(log_file_path).await.unwrap();
    for arg in std::env::args() {
        writeln!(file, "{}", arg).await.unwrap();
    }
    writeln!(file, "----").await.unwrap();
    writeln!(file, "settings: {:?}", settings).await.unwrap();
    writeln!(file, "----").await.unwrap();
    let log_file = Mutex::new(file);
    let args: Vec<_> = std::env::args().skip(1).collect();
    let solver = Command::new(z3_path)
        .arg("trace=true")
        .arg("proof=true")
        // .arg(format!("trace_file_name={}")) TODO: Dump the log files only
        // when required.
        .arg("smt.qi.profile=true")
        .arg("smt.qi.profile_freq=10000")
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let solver_stdin = solver.stdin.expect("failed to create stdin pipe with Z3");
    let solver_stdout = solver.stdout.expect("failed to create stdout pipe with Z3");
    let solver_stderr = solver.stderr.expect("failed to create stderr pipe with Z3");
    // let input = pass_input(&log_file, solver_stdin);
    // let output = pass_output(&log_file, solver_stdout);
    let communicate = communicate(&log_file, solver_stdin, solver_stdout, &settings);
    let error = pass_error(&log_file, solver_stderr);
    // try_join!(input, output, error)?;
    try_join!(communicate, error)?;
    // TODO: Run the SMT log analysis tool and delete the log file unless
    // explicitly asked to keep it.
    Ok(())
}
