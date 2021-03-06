// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// In an ideal world there would be a stable well documented set of crates containing a specific
// version of the Rust compiler along with its sources and debug information. We'd then just get
// those from crate.io and merely go on our way as just another Rust application. Rust compiler
// upgrades will be non events for Mirai until it is ready to jump to another release and old
// versions of Mirai will continue to work just as before.
//
// In the current world, however, we have to use the following hacky feature to get access to a
// private and not very stable set of APIs from whatever compiler is in the path when we run Mirai.
// While pretty bad, it is a lot less bad than having to write our own compiler, so here goes.
#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(vec_remove_item)]

extern crate mirai;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_rayon;
extern crate syntax;
extern crate tempdir;

use mirai::callbacks;
use mirai::utils;
use rustc_rayon::iter::IntoParallelIterator;
use rustc_rayon::iter::ParallelIterator;
use std::fs;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;
use std::path::PathBuf;
use std::str::FromStr;
use syntax::errors::{Diagnostic, DiagnosticBuilder};
use tempdir::TempDir;

// Run the tests in the tests/run-pass directory.
// Eventually, there will be separate test cases for other directories such as compile-fail.
#[test]
fn run_pass() {
    let run_pass_path = PathBuf::from_str("tests/run-pass").unwrap();
    assert_eq!(run_directory(run_pass_path), 0);
}

// Iterates through the files in the directory at the given path and runs each as a separate test
// case. For each case, a temporary output directory is created. The cases are then iterated in
// parallel and run via invoke_driver.
fn run_directory(directory_path: PathBuf) -> usize {
    let sys_root = utils::find_sysroot();
    let mut files_and_temp_dirs = Vec::new();
    for entry in fs::read_dir(directory_path).expect("failed to read run-pass dir") {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        };
        let file_path = entry.path();
        let file_name = entry.file_name();
        let temp_dir = TempDir::new("miraiTest").expect("failed to create a temp dir");
        let temp_dir_path_buf = temp_dir.into_path();
        let output_dir_path_buf = temp_dir_path_buf.join(file_name.into_string().unwrap());
        fs::create_dir(output_dir_path_buf.as_path()).expect("failed to create test output dir");
        files_and_temp_dirs.push((
            file_path.into_os_string().into_string().unwrap(),
            output_dir_path_buf.into_os_string().into_string().unwrap(),
        ));
    }
    files_and_temp_dirs
        .into_par_iter()
        .fold(
            || 0,
            |acc, (file_name, temp_dir_path)| {
                acc + self::invoke_driver(file_name, temp_dir_path, sys_root.clone())
            },
        )
        .reduce(|| 0, |acc, code| acc + code)
}

// Runs the single test case found in file_name, using temp_dir_path as the place
// to put compiler output, which for Mirai includes the persistent summary store.
fn invoke_driver(file_name: String, temp_dir_path: String, sys_root: String) -> usize {
    let f_name = file_name.clone();
    let result = std::panic::catch_unwind(|| {
        rustc_driver::run(|| {
            let f_name = file_name.clone();
            let command_line_arguments: Vec<String> = vec![
                String::from("--crate-name mirai"),
                file_name,
                String::from("--crate-type"),
                String::from("lib"),
                String::from("-C"),
                String::from("debuginfo=2"),
                String::from("--out-dir"),
                temp_dir_path,
                String::from("--sysroot"),
                sys_root,
                String::from("-Z"),
                String::from("span_free_formats"),
                String::from("-Z"),
                String::from("mir-emit-retag"),
                String::from("-Z"),
                String::from("mir-opt-level=0"),
            ];

            let call_backs = callbacks::MiraiCallbacks::with_buffered_diagnostics(
                box move |diagnostics| {
                    let mut expected_errors = ExpectedErrors::new(&f_name);
                    expected_errors.check_messages(diagnostics)
                },
                |db: &mut DiagnosticBuilder, buf: &mut Vec<Diagnostic>| {
                    db.cancel();
                    db.clone().buffer(buf);
                },
            );

            rustc_driver::run_compiler(
                &command_line_arguments,
                box call_backs,
                None, // use default file loader
                None, // emit output to default destination
            )
        })
    });

    match result {
        Ok(_) => 0,
        Err(_) => {
            println!("{} failed", f_name);
            1
        }
    }
}

/// A collection of error strings that are expected for a test case.
struct ExpectedErrors {
    messages: Vec<String>,
}

impl ExpectedErrors {
    /// Reads the file at the given path and scans it for instances of "//~ message".
    /// Each message becomes an element of ExpectedErrors.messages.
    pub fn new(path: &str) -> ExpectedErrors {
        let exp = load_errors(&PathBuf::from_str(&path).unwrap());
        ExpectedErrors { messages: exp }
    }

    /// Checks if the given set of diagnostics matches the expected diagnostics.
    pub fn check_messages(&mut self, diagnostics: &Vec<Diagnostic>) {
        diagnostics.iter().for_each(|diag| {
            self.remove_message(&diag.message());
            for child in &diag.children {
                self.remove_message(&child.message());
            }
        });
        if self.messages.len() > 0 {
            panic!("Expected errors not reported: {:?}", self.messages);
        }
    }

    /// Removes the first element of self.messages and checks if it matches msg.
    fn remove_message(&mut self, msg: &str) {
        if self.messages.remove_item(&String::from(msg)).is_none() {
            panic!("Unexpected error: {} Expected: {:?}", msg, self.messages);
        }
    }
}

/// Scans the contents of test file for patterns of the form "//~ message"
/// and returns a vector of the matching messages.
fn load_errors(testfile: &Path) -> Vec<String> {
    let rdr = BufReader::new(File::open(testfile).unwrap());
    let tag = "//~";
    rdr.lines()
        .enumerate()
        .filter_map(|(_line_num, line)| parse_expected(&line.unwrap(), &tag))
        .collect()
}

/// Returns the message part of the pattern "//~ message" if there is a match, otherwise None.
fn parse_expected(line: &str, tag: &str) -> Option<String> {
    let start = line.find(tag)? + tag.len();
    Some(String::from(line[start..].trim()))
}
