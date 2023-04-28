/*
 * Copyright 2023 Jonáš Fiala <jonas.fiala@inf.ethz.ch>
 * Copyright 2023 taylor.fish <contact@taylor.fish>
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

use compiletest_rs::common::Mode;
use compiletest_rs::{run_tests, Config};
use std::process::Command;

#[test]
fn compile_fail() {
    let mut config = Config::default();
    // Test all files in `src/tests/compiletest_rs/compile_fail`
    config.src_base = "src/tests/compiletest_rs/compile_fail".into();
    // All tests should fail to compile.
    config.mode = Mode::CompileFail;
    // New feature of `compiletest`, ensures that comments
    // for testing purposes are understood properly.
    config.strict_headers = true;

    // Running `cargo test` will build to `target/debug/deps`, but it's quite
    // hard to find the `.rlib` there. Instead, try to build this crate
    // manually so that we have a `.rlib` to link against in `target/debug`.
    let mut features = String::new();
    if cfg!(feature = "fallback") {
        features += "fallback";
    }
    let status = Command::new("cargo")
        .args(&["build", "--features", features.as_str()])
        .status()
        .unwrap();

    if status.success() {
        // There are various problems with using `link_deps` and `clean_rmeta`,
        // if we managed to build the `.rlib` above then we can avoid them.
        config.target_rustcflags = Some("-L target/debug".into());
    } else {
        // Using `link_deps` isn't enough to set `target_rustcflags` due to
        // https://github.com/Manishearth/compiletest-rs/issues/155
        config.target_rustcflags = Some("-L target/debug/deps".into());
        // Populate config.target_rustcflags with dependencies on the path
        config.link_deps();
        // This helps with E0464, but will also invalidate the cache and cause
        // a rebuild the next time. Sometimes E0464 still occurs (e.g. when
        // changing features), in such a case run `cargo clean` and try again.
        config.clean_rmeta();
    }
    run_tests(&config);
}
