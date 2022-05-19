// run-pass

// ignore-windows - this is a unix-specific test
// ignore-emscripten no processes
// ignore-sgx no processes
// ignore-tidy-linelength
use std::os::unix::process::CommandExt;
use std::process::Command;

// `argv` attribute changes each time the test is made so needs to be retrieved dynamically
// There is no public API to access it so we need to parse the debug output
// Example of returned String: "[0x600010bb8000, 0x600010bb80a0]"
fn get_argv(cmd: &Command) -> String {
    format!("{cmd:?}").split_once("Argv(").and_then(|(_, after)| after.split_once(")")).unwrap().0.to_string()
}

fn main() {
    let mut command = Command::new("some-boring-name");

    assert_eq!(format!("{command:?}"), format!(r#"Command {{ program: "some-boring-name", args: ["some-boring-name"], argv: Argv({}), env: CommandEnv {{ clear: false, saw_path: false, vars: {{}} }}, cwd: None, uid: None, gid: None, saw_nul: false, groups: None, stdin: None, stdout: None, stderr: None, pgroup: None }}"#, get_argv(&command)));

    command.args(&["1", "2", "3"]);

    assert_eq!(format!("{command:?}"), format!(r#"Command {{ program: "some-boring-name", args: ["some-boring-name", "1", "2", "3"], argv: Argv({}), env: CommandEnv {{ clear: false, saw_path: false, vars: {{}} }}, cwd: None, uid: None, gid: None, saw_nul: false, groups: None, stdin: None, stdout: None, stderr: None, pgroup: None }}"#, get_argv(&command)));

    command.arg0("exciting-name");

    assert_eq!(format!("{command:?}"), format!(r#"Command {{ program: "some-boring-name", args: ["exciting-name", "1", "2", "3"], argv: Argv({}), env: CommandEnv {{ clear: false, saw_path: false, vars: {{}} }}, cwd: None, uid: None, gid: None, saw_nul: false, groups: None, stdin: None, stdout: None, stderr: None, pgroup: None }}"#, get_argv(&command)));
}
