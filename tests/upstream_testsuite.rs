use std::fmt::Write;
use std::fs::{DirEntry, ReadDir};
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context, Result};
use lazy_regex::regex_captures;

const UPSTREAM_TEST_DIR: &'static str =
    concat!(env!("CARGO_MANIFEST_DIR"), "/../craftinginterpreters/test/");

#[test]
fn run_all_upstream_tests() -> Result<()> {
    let filter = |entry: &DirEntry| {
        ["expressions", "scanning", "benchmark"].contains(&entry.file_name().to_str().unwrap())
    };
    let mut test_cnt = 0;
    for test in UpstreamTestFinder::new(UPSTREAM_TEST_DIR, filter) {
        test?.assert_cmd()?;
        test_cnt += 1;
    }
    println!("Successfully ran {test_cnt} tests.");
    Ok(())
}

#[test]
fn run_single_named() -> Result<()> {
    let test_name = "literals.lox";

    let filter = |entry: &DirEntry| {
        entry.path().is_file() && entry.file_name().to_str().unwrap() != test_name
    };
    let mut test_cnt = 0;
    for test in UpstreamTestFinder::new(UPSTREAM_TEST_DIR, filter) {
        test?.assert_cmd()?;
        test_cnt += 1;
    }
    assert!(test_cnt > 0, "Didn't run a single test.");
    Ok(())
}

struct UpstreamTestFinder<F: FnMut(&DirEntry) -> bool> {
    reject_matching: F,
    dirs: Vec<ReadDir>,
}

impl<F: FnMut(&DirEntry) -> bool> UpstreamTestFinder<F> {
    fn new(root: impl AsRef<Path>, filter: F) -> Self {
        let dirs = vec![std::fs::read_dir(root.as_ref()).unwrap()];
        Self {
            reject_matching: filter,
            dirs,
        }
    }
}

impl<F: FnMut(&DirEntry) -> bool> Iterator for UpstreamTestFinder<F> {
    type Item = Result<TestCase>;

    fn next(&mut self) -> Option<Self::Item> {
        let entry = loop {
            match self.dirs.last_mut()?.next() {
                None => {
                    self.dirs.pop();
                }
                Some(Ok(entry)) if !(self.reject_matching)(&entry) => break entry,
                Some(Err(err)) => return Some(Err(anyhow!(err))),
                _ => {}
            };
        };
        let path = entry.path();
        if path.is_dir() {
            match std::fs::read_dir(path) {
                Ok(readdir) => {
                    self.dirs.push(readdir);
                    self.next()
                }
                Err(err) => return Some(Err(anyhow!(err))),
            }
        } else {
            Some(TestCase::from_path(path))
        }
    }
}

#[cfg(miri)]
fn run_single<P: AsRef<Path>>(p: P) -> Result<()> {
    let source = std::fs::read_to_string(p).unwrap();
    let heap = lox::clox::Heap::new();
    let mut vm = lox::clox::Vm::new(&heap);
    let _ = vm.interpret(source.as_ref()); // some tests are written to cause interpreter errors
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

    #[cfg(not(miri))]
    fn assert_cmd(&self) -> Result<()> {
        (|| -> Result<()> {
            assert_cmd::Command::cargo_bin("clox")?
                .arg("--ci-testsuite")
                .arg("--gc-stress-test")
                .arg(&self.file)
                .assert()
                .try_stdout(self.expect_stdout.clone())?
                .try_stderr(self.expect_stderr.clone())?
                .try_code(self.expect_exit_code)?;
            Ok(())
        })()
        .with_context(|| self.read_source())
    }

    #[cfg(miri)]
    fn assert_cmd(&self) -> Result<()> {
        let source = self.read_source();
        let heap = lox::clox::Heap::new();
        let mut vm = lox::clox::Vm::new(&heap);
        let _ = vm.interpret(source.as_ref()); // some tests are written to cause interpreter errors
        Ok(())
    }

    pub fn read_source(&self) -> String {
        std::fs::read_to_string(&self.file).unwrap()
    }
}
