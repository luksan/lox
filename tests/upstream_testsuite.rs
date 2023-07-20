use std::fmt::Write;
use std::fs::DirEntry;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};
use lazy_regex::regex_captures;

const UPSTREAM_TEST_DIR: &'static str =
    concat!(env!("CARGO_MANIFEST_DIR"), "/../craftinginterpreters/test/");

#[test]
fn run_all_upstream_tests() -> Result<()> {
    let test_cnt = run_tests_recursive(UPSTREAM_TEST_DIR, &mut |entry| {
        ["expressions", "scanning", "benchmark"].contains(&entry.file_name().to_str().unwrap())
    })?;
    println!("Successfully ran {test_cnt} tests.");
    Ok(())
}

#[test]
fn run_single_named() -> Result<()> {
    let test_name = "literals.lox";
    assert!(
        run_tests_recursive(UPSTREAM_TEST_DIR, &mut |entry| {
            entry.path().is_file() && entry.file_name().to_str().unwrap() != test_name
        })? > 0,
        "Didn't run a single test."
    );
    Ok(())
}

fn run_tests_recursive(
    p: impl AsRef<Path>,
    reject_matching: &mut impl FnMut(&DirEntry) -> bool,
) -> Result<usize> {
    let mut test_cnt = 0;
    for t in std::fs::read_dir(p)? {
        let entry = t?;
        if reject_matching(&entry) {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            test_cnt += run_tests_recursive(path, reject_matching)?;
        } else {
            test_cnt += 1;
            run_single(path).with_context(|| format!("Testcase {entry:?} failed."))?;
        }
    }
    Ok(test_cnt)
}

fn run_single<P: AsRef<Path>>(p: P) -> Result<()> {
    let case = TestCase::from_path(p)?;

    (|| -> Result<()> {
        assert_cmd::Command::cargo_bin("clox")?
            .arg("--ci-testsuite")
            .arg("--gc-stress-test")
            .arg(&case.file)
            .assert()
            .try_stdout(case.expect_stdout.clone())?
            .try_stderr(case.expect_stderr.clone())?
            .try_code(case.expect_exit_code)?;
        Ok(())
    })()
    .with_context(|| case.read_source())
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

    pub fn read_source(&self) -> String {
        std::fs::read_to_string(&self.file).unwrap()
    }
}
