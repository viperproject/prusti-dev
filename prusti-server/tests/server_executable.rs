use std::{
    env,
    process::{Command, Stdio},
    thread,
    time::Duration,
};

/// test that the server starts up on a given port and outputs it
#[test]
fn basic_startup() {
    let port = 12323;
    let stdout = run_server_with_port(port);

    assert_eq!(
        stdout.lines().next().expect("at least one line in stdout"),
        &format!("port: {}", port),
        "port message as first stdout line"
    );
}

/// test that the server gets a system-assigned (nonzero) port when started up on port 0 and outputs it
#[test]
fn system_assigned_port() {
    let stdout = run_server_with_port(0);

    let line = stdout.lines().next().expect("at least one line in stdout");

    let port_string = line
        .strip_prefix("port: ")
        .expect("port message as first stdout line");

    assert_ne!(
        port_string.parse::<u16>().expect("valid port number"),
        0,
        "non-zero port number"
    );
}

/// runs the server for a short duration and returns its stdout as a string
fn run_server_with_port(port: u16) -> String {
    let server_path = env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .with_file_name("prusti-server-driver") // can't run prusti-server itself because we need to kill it later, and that wouldn't kill the driver
        .with_extension(env::consts::EXE_EXTENSION);

    let mut server = Command::new(server_path)
        .arg("--port")
        .arg(port.to_string())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to run prusti-server");

    // make sure it can run for 5 seconds, as well as giving it time to start up
    thread::sleep(Duration::from_secs(5));
    server.kill().expect("server stopped prematurely");

    let output = server.wait_with_output().unwrap();
    String::from_utf8(output.stdout).expect("could not parse server stdout as utf-8")
}
