use crate::context::Context;
use async_std::{
    io::{prelude::BufReadExt, BufReader, WriteExt},
    process::{ChildStderr, ChildStdin, ChildStdout},
};

fn are_parens_balanced(line: &str) -> bool {
    let openning_parens = line.chars().filter(|c| *c == '(').count();
    let closing_parens = line.chars().filter(|c| *c == ')').count();
    openning_parens == closing_parens
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

pub(crate) async fn communicate(
    context: &Context,
    mut solver_stdin: ChildStdin,
    solver_stdout: ChildStdout,
) -> Result<(), std::io::Error> {
    let mut stdout = async_std::io::stdout();
    let mut solver_stdout = BufReader::new(solver_stdout);
    let mut response = String::new();
    let mut command = String::new();
    while read_command(&mut command).await? {
        context.write_to_log("in ", &command).await?;
        let now = std::time::Instant::now();
        solver_stdin.write_all(command.as_bytes()).await?;
        solver_stdin.flush().await?;

        assert!(
            read_response(&mut solver_stdout, &mut response)
                .await
                .unwrap(),
            "reached EOF while reading response"
        );
        let elapsed = now.elapsed().as_millis();
        context.write_to_log("out", &response).await?;
        context.write_number_to_log("elapsed-time", elapsed).await?;
        stdout.write_all(response.as_bytes()).await?;
        stdout.flush().await?;

        context.check(&command, &response).await?;
    }

    Ok(())
}

pub(crate) async fn pass_error(
    context: &Context,
    solver_stderr: ChildStderr,
) -> Result<(), std::io::Error> {
    let mut solver_stderr = BufReader::new(solver_stderr);
    let mut stderr = async_std::io::stderr();
    let mut line = String::new();
    context.write_to_log("err", "stderr started\n").await?;
    while solver_stderr.read_line(&mut line).await? > 0 {
        context.write_to_log("err", &line).await?;
        stderr.write_all(line.as_bytes()).await?;
        stderr.flush().await?;
        line.clear();
    }
    context.write_to_log("err", "stderr finished\n").await?;
    Ok(())
}
