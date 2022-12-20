/*
 * Copyright 2022 taylor.fish <contact@taylor.fish>
 *
 * This file is part of tagged-pointer.
 *
 * tagged-pointer is licensed under the Apache License, Version 2.0
 * (the "License"); you may not use tagged-pointer except in compliance
 * with the License. You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::env;
use std::io;
use std::iter::FromIterator;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn compile<P: AsRef<Path>>(path: P) -> io::Result<bool> {
    let mut out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    out.push("feature-test");
    Ok(Command::new(env::var_os("RUSTC").unwrap())
        .arg(path.as_ref())
        .arg("-o")
        .arg(out)
        .arg("--crate-type=lib")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?
        .success())
}

fn main() -> io::Result<()> {
    env::set_current_dir(PathBuf::from_iter(&["misc", "feature-test"]))?;
    if compile("unsafe_op_in_unsafe_fn.rs")? {
        println!("cargo:rustc-cfg=has_unsafe_op_in_unsafe_fn");
    }
    println!("cargo:rerun-if-changed=build.rs");
    Ok(())
}
