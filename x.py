#!/usr/bin/env python3

"""A wrapper for cargo that sets up the Prusti environment."""

import sys
if sys.version_info[0] < 3:
    print('You need to run this script with Python 3.')
    sys.exit(1)

import os
import platform
import subprocess
import glob
import csv
import logging
from pathlib import Path
import time
import json
import signal
import shutil
import traceback
import datetime

sys.path.append(os.path.join(os.path.dirname(__file__), 'scripts'))
import reporting
from reporting import (
    report, error
)
import benchmark
from helper_functions import (
    get_env, run_command, extract_test_compile_flags
)
import verify_test

dry_run = False

RUSTFMT_CRATES = [
    'analysis',
    'jni-gen',
    'prusti',
    'prusti-common',
    'prusti-contracts/prusti-contracts',
    'prusti-contracts/prusti-contracts-proc-macros',
    'prusti-contracts/prusti-specs',
    'prusti-contracts/prusti-std',
    'prusti-contracts-build',
    'prusti-interface',
    'prusti-launch',
    'prusti-rustc-interface',
    'prusti-server',
    'prusti-smt-solver',
    'prusti-tests',
    'prusti-utils',
    #'prusti-viper',
    'smt-log-analyzer',
    #'test-crates',
    'viper',
    'viper-sys',
    'vir',
    'vir-gen',
]

RUSTFMT_PATHS = [
    'vir/defs/mod.rs',
    'prusti-common/src/report/mod.rs',
    'prusti-common/src/utils/mod.rs',
    'prusti-common/src/vir/to_viper.rs',
    'prusti-common/src/vir/low_to_viper/mod.rs',
    'prusti-common/src/vir/optimizations/mod.rs',
    'prusti-viper/src/encoder/foldunfold/mod.rs',
    'prusti-viper/src/encoder/mir/mod.rs',
    'prusti-viper/src/encoder/high/mod.rs',
    'prusti-viper/src/encoder/typed/mod.rs',
    'prusti-viper/src/encoder/middle/mod.rs',
    'prusti-viper/src/encoder/snapshot/mod.rs',
    'prusti-viper/src/encoder/lifetimes/mod.rs',
    'prusti-viper/src/encoder/definition_collector.rs',
    'prusti-viper/src/encoder/counterexamples/mod.rs',
    'vir/defs/mod.rs',
]


def shell(command, term_on_nzec=True):
    """Run a shell command."""
    logging.debug(f"Running a shell command: {command}")
    if not dry_run:
        completed = subprocess.run(command.split())
        if completed.returncode != 0:
            logging.warn(f"Shell command \"{command}\" failed with return code {completed.returncode}")
            if term_on_nzec:
                sys.exit(completed.returncode)
        return completed.returncode


def cargo(args):
    """Run cargo with the given arguments."""
    run_command(['cargo'] + args)


def viper_version():
    with open("viper-toolchain", "r") as file:
        return file.read().strip()


def setup_ubuntu(install_deps: bool):
    """Install the dependencies on Ubuntu."""
    # Install dependencies.
    if install_deps:
        shell('sudo apt-get update')
        shell('sudo apt-get install -y '
            'build-essential pkg-config '
            'curl gcc libssl-dev unzip')
    # Download Viper.
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsLinux.zip -Lo ViperToolsLinux.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    shell('unzip ViperToolsLinux.zip -d viper_tools')
    os.remove('ViperToolsLinux.zip')


def setup_linux():
    """Install the dependencies on generic Linux."""
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsLinux.zip -Lo ViperToolsLinux.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    shell('unzip ViperToolsLinux.zip -d viper_tools')
    os.remove('ViperToolsLinux.zip')


def setup_mac():
    """Install the dependencies on Mac."""
    # Non-Viper dependencies must be installed manually.
    # Download Viper.
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsMac.zip -Lo ViperToolsMac.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    shell('unzip ViperToolsMac.zip -d viper_tools')
    os.remove('ViperToolsMac.zip')


def setup_win():
    """Install the dependencies on Windows."""
    # Non-Viper dependencies must be installed manually.
    # Download Viper.
    shell(
        'curl https://github.com/viperproject/viper-ide/releases/'
        'download/{}/ViperToolsWin.zip -Lo ViperToolsWin.zip'.format(viper_version())
    )
    if os.path.exists('viper_tools'):
        shutil.rmtree('viper_tools')
    os.mkdir('viper_tools')
    shell('tar -xf ViperToolsWin.zip -C viper_tools')
    os.remove('ViperToolsWin.zip')


def setup_rustup():
    # Update rustup
    # shell('rustup self update', term_on_nzec=False)
    # Install toolchain
    shell('rustup show', term_on_nzec=False)


def setup(args):
    """Install the dependencies."""
    install_deps = True
    if len(args) == 1 and args[0] == '--dry-run':
        global dry_run
        dry_run = True
    elif len(args) == 1 and args[0] == '--no-deps':
        install_deps = False
    elif args:
        error("unexpected arguments: {}", args)
    if sys.platform in ("linux", "linux2"):
        if 'Ubuntu' in platform.version():
            setup_ubuntu(install_deps)
        else:
            setup_linux()
    elif sys.platform == "darwin":
        setup_mac()
    elif sys.platform == "win32":
        setup_win()
    else:
        error("unsupported platform: {}", sys.platform)
    setup_rustup()


def clean(args):
    """Delete all temporary files."""
    run_cargo_clean = True
    if len(args) == 1 and args[0] == '--skip-cargo-clean':
        run_cargo_clean = False
    elif args:
        error("unexpected arguments: {}", args)
    if os.path.exists('prusti-contracts/target'):
        shutil.rmtree('prusti-contracts/target')
    if os.path.exists('log'):
        shutil.rmtree('log')
    if run_cargo_clean:
        cargo(['clean'])


def ide(args):
    """Start VS Code with the given arguments."""
    run_command(['code'] + args)


def run_viper_server(port=None):
    """Start the Viper server."""
    env = get_env()
    viper_home = env['VIPER_HOME']
    jar_path = glob.glob(os.path.join(viper_home, '*.jar'))
    command = ['java', '-Xmx512m', '-Xss512m', '-jar', ':'.join(jar_path)]
    if port is not None:
        command.extend(['--port', str(port)])
    run_command(command)


def clippy_in(cwd):
    """Run cargo clippy in given subproject."""
    run_command(['cargo', 'clippy', '--', '-D', 'warnings'], cwd=cwd)

def fmt_in(cwd):
    """Run cargo fmt in given subproject."""
    run_command(['cargo', 'fmt'], cwd=cwd)

def fmt_all():
    """Run rustfmt on all formatted files."""
    for crate in RUSTFMT_CRATES:
        fmt_in(crate)
    for path in RUSTFMT_PATHS:
        for file in glob.glob(path, recursive=True):
            run_command(['rustfmt', file])

def fmt_check_in(cwd):
    """Run cargo fmt check in the given subproject."""
    run_command(['cargo', 'fmt', '--', '--check'], cwd=cwd)

def fmt_check_all():
    """Run rustfmt check on all formatted files."""
    for crate in RUSTFMT_CRATES:
        fmt_check_in(crate)
    for path in RUSTFMT_PATHS:
        for file in glob.glob(path, recursive=True):
            run_command(['rustfmt', '--check', file])

def check_smir():
    """Check that `extern crate` is used only in `prusti_rustc_interface` (TODO: `prusti_interface` is also ignored for now)."""
    for folder in os.listdir('.'):
        if folder == 'prusti-rustc-interface' or folder == 'prusti-interface':
            continue
        if os.path.exists(os.path.join(folder, 'Cargo.toml')):
            completed = subprocess.run(
                ['grep', 'extern crate', '-nr', folder],
                capture_output=True
            )
            lines = [
                line
                for line in completed.stdout.decode().splitlines()
                if '.rs:' in line and not line.startswith('prusti-tests/tests')
            ]
            assert not lines, (
                'found `extern crate` outside '
                'prusti_rustc_interface:\n{}'.format(
                    '\n'.join(lines)
                )
            )

def package(mode: str, package_path: str):
    """Packages Prusti artifacts in the `package_path` folder.

    Args:
      mode: Either 'debug' or 'release'.
      package_path: Where to copy all Prusti files and dependencies.
    """
    logging.info(f"Preparing a {mode}-mode Prusti package in '{package_path}'.")

    # Prepare destination folder
    Path(package_path).mkdir(parents=True, exist_ok=True)
    if os.listdir(package_path):
        logging.warning(f"The destination folder '{package_path}' is not empty.")

    # The glob patterns of the files to copy and their destination folder inside the package.
    include_paths_and_dst = [
        # (source pattern, destination)
        ("rust-toolchain", "."),
        ("viper_tools", "."),
        (f"target/{mode}/prusti-driver*", "."),
        (f"target/{mode}/prusti-server*", "."),
        (f"target/{mode}/prusti-rustc*", "."),
        (f"target/{mode}/cargo-prusti*", "."),
        (f"target/verify/{mode}/libprusti_contracts.*", "."),
        (f"target/verify/{mode}/deps/libprusti_contracts_proc_macros-*", "deps"),
        (f"target/verify/{mode}/deps/prusti_contracts_proc_macros-*.dll", "deps"),
        (f"target/verify/{mode}/libprusti_std.*", "."),
        (f"target/verify/{mode}/deps/libprusti_contracts-*", "deps"),
        (f"target/verify/{mode}/deps/prusti_contracts-*.dll", "deps"),
    ]
    exclude_paths = [
        f"target/{mode}/*.d",
        f"target/verify/{mode}/*.d",
        f"target/verify/{mode}/deps/*.d",
    ]
    actual_exclude_set = set(path for pattern in exclude_paths for path in glob.glob(pattern))
    logging.debug(f"The number of excluded paths is: {len(actual_exclude_set)}")

    # Copy the paths
    num_copied_paths = 0
    for pattern, dst_folder in include_paths_and_dst:
        matched_paths = set(glob.glob(pattern))
        if not matched_paths:
            logging.debug(f"A glob pattern gave no results: {pattern}")
        filtered_paths = sorted(matched_paths - actual_exclude_set)
        for src_path in filtered_paths:
            dst_folder_path = os.path.join(package_path, dst_folder)
            dst_path = os.path.join(dst_folder_path, os.path.basename(src_path))
            logging.info(f"Copying '{src_path}' to '{dst_path}'...")
            num_copied_paths += 1
            if os.path.isfile(src_path):
                Path(dst_folder_path).mkdir(parents=True, exist_ok=True)
                shutil.copy(src_path, dst_path)
            else:
                if os.path.exists(dst_path):
                    shutil.rmtree(dst_path)
                shutil.copytree(src_path, dst_path)

    logging.info(f"Copied {num_copied_paths} paths to the package folder")
    if num_copied_paths <= 11:
        logging.error(f"The number of copied paths is too low.")
        sys.exit(1)


def test_package(package_path: str):
    """Quickly test that a Prusti release has been packaged correctly.

    Args:
      package_path: The path of the package.
    """
    prusti_rustc_path = os.path.join(package_path, "prusti-rustc")
    if sys.platform == "win32":
        prusti_rustc_path += ".exe"
    os.chmod(prusti_rustc_path, 0o744)
    test_files = [
        (True, "prusti-tests/tests/verify_overflow/pass/simple-specs/simple-spec.rs"),
        (False, "prusti-tests/tests/verify/fail/simple-specs/binary-search.rs"),
    ]
    for should_pass, test_path in test_files:
        logging.info(f"Testing '{prusti_rustc_path}' on '{test_path}'")
        status = subprocess.run(
            [prusti_rustc_path, test_path, "--edition=2018"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        exit_code = status.returncode
        if (exit_code == 0) != should_pass:
            logging.error(
                f"The test is marked as {should_pass=}, but the exit code is {exit_code}.\n"
                "┌─── Begin stdout ───┐\n"
                f"{status.stdout.decode('utf-8')}\n"
                "└─── End stdout ─────┘\n"
                "┌─── Begin stderr ───┐\n"
                f"{status.stderr.decode('utf-8')}\n"
                "└─── End stderr ─────┘"
            )
            sys.exit(1)


def main(argv):
    logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.DEBUG)
    for i, arg in enumerate(argv):
        if arg.startswith('+'):
            if arg == '+v' or arg == '++verbose':
                reporting.verbose = True
                continue
            else:
                error('unknown option: {}', arg)
        elif arg == 'setup':
            setup(argv[i+1:])
            break
        elif arg == 'clean':
            clean(argv[i+1:])
            break
        elif arg == 'ide':
            ide(argv[i+1:])
            break
        elif arg == 'run-benchmarks':
            cargo(['build', '--all', '--release'])
            benchmark.run_benchmarks(argv[i+1:])
            break
        elif arg == 'run-viper-server':
            run_viper_server(*argv[i+1:])
            break
        elif arg == 'verify-test':
            verify_test.verify_test(argv[i+1:])
            break
        elif arg == 'exec':
            run_command(argv[i+1:])
            break
        elif arg == 'clippy-in':
            clippy_in(*argv[i+1:])
            break
        elif arg == 'fmt-check':
            fmt_check_in(*argv[i+1:])
            break
        elif arg == 'fmt-check-all':
            fmt_check_all(*argv[i+1:])
            break
        elif arg == 'fmt':
            fmt_in(*argv[i+1:])
            break
        elif arg == 'fmt-all':
            fmt_all(*argv[i+1:])
            break
        elif arg == 'check-smir':
            check_smir(*argv[i+1:])
            break
        elif arg == 'package':
            package(*argv[i+1:])
            break
        elif arg == 'test-package':
            test_package(*argv[i+1:])
            break
        else:
            cargo(argv[i:])
            break
    if not argv:
        cargo(argv)


if __name__ == '__main__':
    main(sys.argv[1:])
