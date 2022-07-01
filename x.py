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
    #'prusti-common',
    #'prusti-contracts',
    'prusti-contracts-impl',
    'prusti-contracts-internal',
    'prusti-contracts-test',
    #'prusti-interface',
    'prusti-launch',
    'prusti-rustc-interface',
    'prusti-server',
    'prusti-smt-solver',
    #'prusti-specs',
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
    'prusti-common/src/report/mod.rs',
    'prusti-common/src/utils/mod.rs',
    'prusti-common/src/vir/to_viper.rs',
    'prusti-common/src/vir/low_to_viper/mod.rs',
    'prusti-common/src/vir/optimizations/mod.rs',
    'prusti-interface/src/environment/mir_dump/mod.rs',
    'prusti-interface/src/environment/mir_analyses/mod.rs',
    'prusti-interface/src/environment/mir_sets/mod.rs',
    'prusti-interface/src/environment/mir_body/mod.rs',
    'prusti-interface/src/environment/debug_utils/mod.rs',
    'prusti-interface/src/environment/mir_utils/mod.rs',
    'prusti-tests/tests/verify_partial/**/*.rs',
    'prusti-viper/src/encoder/foldunfold/mod.rs',
    'prusti-viper/src/encoder/mir/mod.rs',
    'prusti-viper/src/encoder/high/mod.rs',
    'prusti-viper/src/encoder/middle/mod.rs',
    'prusti-viper/src/encoder/snapshot/mod.rs',
    'prusti-viper/src/encoder/lifetimes/mod.rs',
    'prusti-viper/src/encoder/definition_collector.rs',
    'vir/defs/high/mod.rs',
    'vir/defs/middle/mod.rs',
    'vir/defs/polymorphic/mod.rs',
    'vir/defs/components/mod.rs',
    'vir/defs/snapshot/mod.rs',
    'vir/defs/low/mod.rs',
]


def shell(command, term_on_nzec=True):
    """Run a shell command."""
    print("Running a shell command: ", command)
    if not dry_run:
        completed = subprocess.run(command.split())
        if completed.returncode != 0 and term_on_nzec:
            sys.exit(completed.returncode)
        return completed.returncode


def cargo(args):
    """Run cargo with the given arguments."""
    run_command(['cargo'] + args)


def viper_version():
    with open("viper-toolchain", "r") as file:
        return file.read().strip()


def setup_ubuntu():
    """Install the dependencies on Ubuntu."""
    # Install dependencies.
    shell('sudo apt-get update')
    shell('sudo apt-get install -y '
          'build-essential pkg-config '
          'curl gcc libssl-dev')
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
    shell('rustup self update', term_on_nzec=False)


def setup(args):
    """Install the dependencies."""
    rustup_only = False
    if len(args) == 1 and args[0] == '--dry-run':
        global dry_run
        dry_run = True
    elif len(args) == 1 and args[0] == '--rustup-only':
        rustup_only = True
    elif args:
        error("unexpected arguments: {}", args)
    if not rustup_only:
        if sys.platform in ("linux", "linux2"):
            if 'Ubuntu' in platform.platform():
                setup_ubuntu()
            else:
                setup_linux()
        elif sys.platform == "darwin":
            setup_mac()
        elif sys.platform == "win32":
            setup_win()
        else:
            error("unsupported platform: {}", sys.platform)
    setup_rustup()


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
    """Check that `extern crate` is used only in `prusti_rustc_interface`."""
    for folder in os.listdir('.'):
        if folder == 'prusti-rustc-interface':
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

def main(argv):
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
        else:
            cargo(argv[i:])
            break
    if not argv:
        cargo(argv)


if __name__ == '__main__':
    main(sys.argv[1:])
