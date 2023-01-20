use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering::SeqCst;

use anyhow::{bail, Context, Result};
use lazy_regex::regex_captures;

const PROJ_ROOT: &'static str = env!("CARGO_MANIFEST_DIR");

#[test]
fn run_all_tests() -> Result<()> {
    let test_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../craftinginterpreters/test/");
    run_tests_recursive(test_dir)?;
    println!("Successfully ran {} tests.", TEST_CTR.load(SeqCst));
    Ok(())
}

static TEST_CTR: AtomicU64 = AtomicU64::new(0);

fn run_tests_recursive(p: impl AsRef<Path>) -> Result<()> {
    for t in std::fs::read_dir(p)? {
        let entry = t?;
        if ["expressions", "scanning", "benchmark"].contains(&entry.file_name().to_str().unwrap()) {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            run_tests_recursive(path)?;
        } else {
            TEST_CTR.fetch_add(1, SeqCst);
            run_single(path).with_context(|| format!("Testcase {entry:?} failed."))?;
        }
    }
    Ok(())
}

macro_rules! bail_ne {
    ($expect:expr, $actual:expr, $msg:expr) => {
        if $expect != $actual {
            bail!(format!(
                "{} : \n  expected {:?}\n  actual   {:?}",
                $msg, $expect, $actual
            ))
        }
    };
}

fn run_single<P: AsRef<Path>>(p: P) -> Result<()> {
    let case = TestCase::from_path(p)?;

    let mut lox = PathBuf::from(PROJ_ROOT);
    lox.push("target");
    lox.push("release");
    lox.push("clox");
    let output = Command::new(lox)
        .arg("--ci-testsuite")
        .arg(case.file)
        .output()?;
    let stdout = std::str::from_utf8(&output.stdout)?;
    bail_ne!(case.expect_stdout, stdout, "stdout");
    let stderr = std::str::from_utf8(&output.stderr)?;
    bail_ne!(case.expect_stderr, stderr, "stderr");
    bail_ne!(
        Some(case.expect_exit_code),
        output.status.code(),
        "exit code"
    );

    Ok(())
}

struct TestCase {
    file: PathBuf,
    expect_stdout: String,
    expect_stderr: String,
    expect_exit_code: i32,
}

impl TestCase {
    pub fn from_path(p: impl AsRef<Path>) -> Result<Self> {
        let file = p.as_ref().to_path_buf();

        let mut expect_stdout = String::new();
        let mut expect_stderr = String::new();
        let mut expect_exit_code = 0;

        for (num, line) in std::fs::read_to_string(p)?.lines().enumerate() {
            if let Some((_, stdout)) = regex_captures!("// expect: ?(.*)", line) {
                writeln!(&mut expect_stdout, "{stdout}")?;
            } else if let Some((_, error)) = regex_captures!("// (Error.*)", line) {
                writeln!(&mut expect_stderr, "[line {}] {error}", num + 1)?;
                expect_exit_code = 65;
            } else if let Some((_, _, java_or_c, line_no, error)) =
                regex_captures!(r"// \[((java|c) )?line (\d+)\] (Error.*)", line)
            {
                if java_or_c != "java" {
                    writeln!(&mut expect_stderr, "[line {line_no}] {error}")?;
                }
                expect_exit_code = 65;
            } else if let Some((_, error)) = regex_captures!("// expect runtime error: (.+)", line)
            {
                writeln!(&mut expect_stderr, "{error}\n[line {}] in script", num + 1)?;
                expect_exit_code = 70;
            } else if let Some((_, num, error)) =
                regex_captures!(r"\[.*line (\d+)\] (Error.+)", line)
            {
                writeln!(&mut expect_stderr, "[line {num}] {error}")?;
                expect_exit_code = 65;
            } else if let Some((_, _num)) = regex_captures!(r"\[line (\d+)\]", line) {
                // stack trace
                expect_exit_code = 65;
            }
        }

        Ok(Self {
            file,
            expect_stdout,
            expect_stderr,
            expect_exit_code,
        })
    }
}
