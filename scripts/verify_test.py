"""The verify-test functionality of `x.py`."""


import argparse
import csv
import json
import glob
import os
from reporting import (
    report, error
)
from helper_functions import (
    get_env, run_command, extract_test_compile_flags
)


def select_newest_file(paths):
    """Select a file that exists and has the newest modification timestamp."""
    existing_paths = [
        (os.path.getmtime(path), path)
        for path in paths if os.path.exists(path)
    ]
    try:
        return next(reversed(sorted(existing_paths)))[1]
    except:
        error("Could not select the newest file from {}", paths)


def generate_launch_json(args_file, env_file):
    """Generates debugging configuration for VS Code extension CodeLLDB.

    https://marketplace.visualstudio.com/items?itemName=vadimcn.vscode-lldb
    """
    with open(args_file) as fp:
        args = fp.read().splitlines()
    with open(env_file) as fp:
        env = dict(
            row.split('=', 1)
            for row in fp.read().splitlines()
        )
    prusti_driver_configuration = {
        "type": "lldb",
        "request": "launch",
        "name": "Debug executable 'prusti-driver'",
        "cargo": {
            "args": [
                "build",
                "--bin=prusti-driver",
                "--package=prusti"
            ],
            "filter": {
                "name": "prusti-driver",
                "kind": "bin"
            }
        },
        "args": args,
        "cwd": "${workspaceFolder}",
        "env": env,
    }
    content = {
        "version": "0.2.0",
        "configurations": [
            prusti_driver_configuration
        ]
    }
    os.makedirs('.vscode', exist_ok=True)
    with open('.vscode/launch.json', 'w') as fp:
        json.dump(content, fp, indent=2)

def analyze_quantifier_logs(test_path):
    test_file_name = os.path.basename(test_path)

#   smt2_directories = glob.glob(os.path.join('log', 'viper_tmp', f'{test_file_name}_*'))
#   for directory in smt2_directories:
#       smt2_files = list(sorted(glob.glob(os.path.join(directory, '*.smt2'))))
#       assert len(smt2_files) == 2
#       print(smt2_files)
    print('the log files are in the following directories:')
    z3_trace_directories = glob.glob(os.path.join('log', 'smt', f'{test_file_name}_*'))
    for directory in z3_trace_directories:
        z3_trace_files = sorted(glob.glob(os.path.join(directory, 'trace*.log')))
        assert len(z3_trace_files) == 2
        wrapper_files = list(sorted(glob.glob(os.path.join(directory, 'wrapper*.log'))))
        for wrapper_file in wrapper_files:
            with open(wrapper_file) as fp:
                counts = {}
                for line in fp:
                    if line.startswith('elapsed-time: '):
                        duration = int(line[14:-1])
                        if duration not in counts:
                            counts[duration] = 1
                        else:
                            counts[duration] += 1
            with open(f'{wrapper_file}.durations.csv', 'w') as fp:
                writer = csv.writer(fp)
                writer.writerow(['Elapsed in miliseconds', 'Count'])
                for duration, count in sorted(counts.items()):
                    writer.writerow([duration, count])

        print(directory)


def parse_args(args):
    parser = argparse.ArgumentParser(description="Verify a test")
    parser.add_argument('test_file', help='the test file to run')
    parser.add_argument(
        "--analyze-quantifiers",
        type=bool,
        const=True,
        default=False,
        nargs='?',
        help="analyze the quantifier information",
    )
    return parser.parse_args(args)

def verify_test(args):
    """Runs prusti on the specified files."""
    args = parse_args(args)
    current_path = os.path.abspath(os.path.curdir)
    candidate_prusti_paths = [
        os.path.join(current_path, 'target', 'release', 'prusti-rustc'),
        os.path.join(current_path, 'target', 'debug', 'prusti-rustc')
    ]
    prusti_path = select_newest_file(candidate_prusti_paths)
    report("Selected Prusti: {}", prusti_path)
    if args.test_file.startswith('prusti-tests/'):
        test_path = args.test_file
    else:
        candidate_test_paths = glob.glob(os.path.join(
            current_path, "prusti-tests/tests*/*", args.test_file))
        if len(candidate_test_paths) == 0:
            error("Not tests found that match: {}", args.test_file)
        elif len(candidate_test_paths) > 1:
            error(
                "Expected one test, but found {} tests that match {}. First 5: {}",
                len(candidate_test_paths),
                args.test_file,
                candidate_test_paths[:5]
            )
        test_path = candidate_test_paths[0]
    report("Found test: {}", test_path)
    compile_flags = extract_test_compile_flags(test_path)
    env = get_env()
    if 'prusti-tests/tests/verify_overflow/' in test_path:
        env['PRUSTI_CHECK_OVERFLOWS'] = 'true'
    else:
        env['PRUSTI_CHECK_OVERFLOWS'] = 'false'
    report("env: PRUSTI_CHECK_OVERFLOWS={}", env['PRUSTI_CHECK_OVERFLOWS'])
    os.makedirs('log/config', exist_ok=True)
    env['PRUSTI_ENCODE_UNSIGNED_NUM_CONSTRAINT'] = 'true'
    env['PRUSTI_RUSTC_LOG_ARGS'] = 'log/config/prusti-rustc-args'
    env['PRUSTI_RUSTC_LOG_ENV'] = 'log/config/prusti-rustc-env'
    if args.analyze_quantifiers:
        env['PRUSTI_USE_SMT_WRAPPER'] = 'true'
        env['PRUSTI_PRESERVE_SMT_TRACE_FILES'] = 'true'
        env['PRUSTI_WRITE_SMT_STATISTICS'] = 'true'
        env['PRUSTI_LOG_SMT_WRAPPER_INTERACTION'] = 'true'
        env['PRUSTI_NUMBER_OF_PARALLEL_VERIFIERS'] = '1'
    def verify_test_on_exit():
        generate_launch_json(
            'log/config/prusti-rustc-args',
            'log/config/prusti-rustc-env'
        )
        if args.analyze_quantifiers:
            analyze_quantifier_logs(test_path)
    run_command(
        [prusti_path, '--edition=2018', test_path] + compile_flags,
        env,
        on_exit=verify_test_on_exit,
        report_time=True,
    )
