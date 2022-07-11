"""The benchmarking functionality of `x.py`."""

import argparse
import csv
import json
import os
import signal
import sys
import subprocess
import time
from reporting import (
    report, error
)
from helper_functions import (
    get_env, run_command, extract_test_compile_flags
)


def get_prusti_server_path_for_benchmark():
    project_root_dir = os.path.dirname(os.path.realpath(sys.argv[0]))

    if sys.platform in ("linux", "linux2"):
        return os.path.join(project_root_dir, 'target', 'release', 'prusti-server-driver')
    else:
        error("unsupported platform for benchmarks: {}", sys.platform)


def get_prusti_rustc_path_for_benchmark():
    project_root_dir = os.path.dirname(os.path.realpath(sys.argv[0]))

    if sys.platform in ("linux", "linux2"):
        return os.path.join(project_root_dir, 'target', 'release', 'prusti-rustc')
    else:
        error("unsupported platform for benchmarks: {}", sys.platform)


def measure_prusti_time(log_file, input_path, env):
    env = dict(env) # Make a copy.
    prusti_rustc_exe = get_prusti_rustc_path_for_benchmark()
    if input_path.startswith('prusti-tests/tests/verify/pass'):
        env['PRUSTI_CHECK_OVERFLOWS'] = 'false'
    elif input_path.startswith('prusti-tests/tests/verify_overflow/pass'):
        env['PRUSTI_CHECK_OVERFLOWS'] = 'true'
    else:
        error('file in an unsupported directory: {}', input_path)
    start_time = time.perf_counter()
    flags = extract_test_compile_flags(input_path)
    command = [prusti_rustc_exe,"--edition=2018", input_path] + flags
    run_command(command, env=env)
    end_time = time.perf_counter()
    elapsed = end_time - start_time
    log_file.write(f"command={command}\n")
    log_file.write(f"env={env}\n")
    log_file.write(f"start_time={start_time}\n")
    log_file.write(f"end_time={end_time}\n")
    log_file.write(f"elapsed={elapsed}\n\n")
    log_file.flush()
    return elapsed


def parse_args(args):
    parser = argparse.ArgumentParser(description="Benchmark Prusti.")
    parser.add_argument(
        "--report-name-suffix",
        default='',
        help="what suffix to add to the report file names",
    )
    parser.add_argument(
        "--warmup-path",
        default="prusti-tests/tests/verify/pass/quick/fibonacci.rs",
        help="the file to use for warm-up",
    )
    parser.add_argument(
        "--warmup-iterations",
        type=int,
        default=6,
        help="how many iterations to use for a warm-up (default: 6)",
    )
    parser.add_argument(
        "--bench-iterations",
        type=int,
        default=10,
        help="how many iterations to use for a benchmarking (default: 10)",
    )
    parser.add_argument(
        "--prusti-server-port",
        type=int,
        default=12345,
        help="how many iterations to use for a benchmarking (default: 12345)",
    )
    parser.add_argument(
        "--report-dir",
        default="benchmark-output",
        help="to which directory to save the report",
    )
    parser.add_argument(
        "--benchmark-csv",
        default="benchmarked-files.csv",
        help="the CSV file containing the tests to be benchmarked",
    )
    parser.add_argument(
        "--log-file",
        default="benchmark-output/log",
        help="the file to which the log is dumped; note that it is overwritten!",
    )
    return parser.parse_args(args)


def run_benchmarks(args):
    """Run the benchmarks and report the time in a json file"""
    args = parse_args(args)
    prusti_server_exe = get_prusti_server_path_for_benchmark()
    server_port = str(args.prusti_server_port)
    output_dir = args.report_dir
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    results = {}
    env = get_env()
    env['PRUSTI_ENABLE_CACHE'] = 'false'
    report("Starting prusti-server ({})", prusti_server_exe)
    server_args = [prusti_server_exe, "--port", server_port]
    server_process = subprocess.Popen(server_args, env=env)
    time.sleep(2)
    if server_process.poll() != None:
        raise RuntimeError('Could not start prusti-server')

    env["PRUSTI_SERVER_ADDRESS"]="localhost:" + server_port
    try:
        with open(args.log_file, 'w') as log_file:
            report("Starting warmup of the server")
            for i in range(args.warmup_iterations):
                t = measure_prusti_time(log_file, args.warmup_path, env)
                report("warmup run {} took {}", i + 1, t)

            report("Finished warmup. Starting benchmark")
            with open(args.benchmark_csv) as csv_file:
                csv_reader = csv.reader(csv_file, delimiter=',')
                for row in csv_reader:
                    file_path = row[0]
                    results[file_path] = []
                    report("Starting to benchmark {}", file_path)
                    for i in range(args.bench_iterations):
                        t = measure_prusti_time(log_file, file_path, env)
                        results[file_path].append(t)
    finally:
        report("terminating prusti-server")
        server_process.send_signal(signal.SIGINT)

    json_result = json.dumps(results, indent = 2)
    timestamp = time.time()
    output_file = os.path.join(
        output_dir, "benchmark" + args.report_name_suffix + str(timestamp) + ".json"
    )
    with open(output_file, "w") as outfile:
        outfile.write(json_result)

    report("Wrote results of benchmark to {}", output_file)
