// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

extern crate core;

use std::env;
use std::fs::copy;
use std::path::{Path, PathBuf};

fn main() {
    let source_file_path = get_z3_lib_file_name();
    let target_file_path = get_target_file_name();
    copy(source_file_path, target_file_path).unwrap();
}

#[cfg(target_os = "macos")]
fn get_z3_lib_file_name() -> PathBuf {
    get_source_path().join("libz3.dylib")
}

#[cfg(target_os = "linux")]
fn get_z3_lib_file_name() -> PathBuf {
    get_source_path().join("libz3.so")
}

fn get_source_path() -> PathBuf {
    let deps = get_deps_path();
    let base = deps.parent().unwrap().parent().unwrap().parent().unwrap();
    base.join("z3/build")
}

#[cfg(target_os = "macos")]
fn get_target_file_name() -> PathBuf {
    get_deps_path().join("libz3.dylib")
}

#[cfg(target_os = "linux")]
fn get_target_file_name() -> PathBuf {
    get_deps_path().join("libz3.so")
}

fn get_deps_path() -> PathBuf {
    let out_dir = env::var("OUT_DIR").unwrap();
    let base = Path::new(&out_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    base.join("deps")
}
