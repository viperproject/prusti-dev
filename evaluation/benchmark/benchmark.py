#/usr/bin/python3

"""
Mounting directories as RAMFS::

    sudo mount -t ramfs -o size=512m ramfs ./log/
    sudo mount -t ramfs -o size=512m ramfs ./nll-facts/
    sudo chmod 777 ./log ./nll-facts

"""

import csv
import datetime
import glob
import os
import subprocess
import time
import re

ROOT = os.path.dirname(os.path.abspath(__file__))
REPOSITORY_ROOT = os.path.join(ROOT, '..', '..')
TOML_FILE = os.path.join(REPOSITORY_ROOT, 'Prusti.toml')
LOG_FILE = os.path.join(ROOT, 'bench.csv')
MAKE_FLAGS = [] # ["JAVA_HOME=/usr/lib/jvm/jdk-11.0.1/"]
ENV_VARS = dict(os.environ,
    # Z3_EXE='/home/software/z3/z3-4.8.3.74db2f250907-x64-ubuntu-14.04/bin/z3',
    # Z3_EXE=os.path.abspath(os.path.join(ROOT, '../../z3/bin/z3')),
    # VIPER_HOME=os.path.abspath(os.path.join(ROOT, '../../viper')),
    RUST_LOG="prusti_viper=info"
)

MANUAL_EVALUATION="""
prusti/tests/verify/pass-overflow/rosetta/100_doors_generic.rs
prusti/tests/verify/pass-overflow/rosetta/Binary_search_shared.rs
prusti/tests/verify/pass-overflow/rosetta/Heapsort_generic.rs
prusti/tests/verify/pass-overflow/rosetta/Knights_tour_generic.rs
prusti/tests/verify/pass-overflow/rosetta/Knuth_shuffle.rs
prusti/tests/verify/pass-overflow/rosetta/Langtons_ant.rs
prusti/tests/verify/pass-overflow/rosetta/Selection_sort_generic.rs

prusti/tests/verify/pass/rosetta/Ackermann_function.rs
prusti/tests/verify/pass-overflow/rosetta/Binary_search_shared_monomorphised.rs
prusti/tests/verify/pass/rosetta/Fibonacci_sequence.rs
prusti/tests/verify/pass/rosetta/Knapsack_Problem.rs
prusti/tests/verify/pass/larger/first-final.rs
prusti/tests/verify/pass-overflow/rosetta/Selection_sort.rs
prusti/tests/verify/pass-overflow/rosetta/Towers_of_Hanoi_spec.rs

prusti/tests/verify/pass-overflow/nll-rfc/borrow_first.rs
prusti/tests/verify/fail/nll-rfc/message.rs
""".strip().split()


def create_configuration_file(check_binary):
    with open(TOML_FILE, 'w') as fp:
        fp.write(
'''
DUMP_DEBUG_INFO = false
DUMP_BORROWCK_INFO = false
CHECK_BINARY_OPERATIONS = {}
'''.format(check_binary))


def build_project():
    cmd = [
            "make",
            "clean",
            ]# + MAKE_FLAGS
    print(' '.join(cmd))
    subprocess.run(
        cmd,
        cwd=ROOT,
        check=True,
        # env=ENV_VARS,
    )
    subprocess.run(
        [
            "make",
            "release",
            ] + MAKE_FLAGS,
        cwd=ROOT,
        check=True,
        # env=ENV_VARS,
    )


def get_benchmarks():
    rosetta_path = os.path.join(ROOT, 'tests/verify/pass/rosetta/')
    rosetta_glob = os.path.join(rosetta_path, '*.rs')
    rosetta_overflow_path = os.path.join(ROOT, 'tests/verify/pass-overflows/rosetta/')
    rosetta_overflow_glob = os.path.join(rosetta_overflow_path, '*.rs')
    rosetta_todo_glob = os.path.join(rosetta_path, 'todo', '*.rs')
    rosetta_stress_path = os.path.join(ROOT, 'tests/verify/todo/stress/rosetta/')
    rosetta_stress_glob = os.path.join(rosetta_stress_path, '*.rs')
    paper_path = os.path.join(ROOT, 'tests/verify/pass/paper-examples/')
    paper_glob = os.path.join(paper_path, '*.rs')
    nll_path = os.path.join(ROOT, 'tests/verify/pass/nll-rfc/')
    nll_glob = os.path.join(nll_path, '*.rs')
    evaluation_path = os.path.join(ROOT, 'tests/verify/pass/evaluation/')
    evaluation_glob = os.path.join(evaluation_path, '*.rs')
    evaluation_overflow_path = os.path.join(ROOT, 'tests/verify/pass-overflows/evaluation/')
    evaluation_overflow_glob = os.path.join(evaluation_overflow_path, '*.rs')
    # return (list(glob.glob(rosetta_glob)) +
            # list(glob.glob(rosetta_todo_glob)) +
            # list(glob.glob(rosetta_stress_glob)) +
            # list(glob.glob(paper_glob)) +
            # list(glob.glob(evaluation_glob)) +
            # list(glob.glob(evaluation_overflow_glob)) +
            # list(glob.glob(nll_glob)))
    # return (list(glob.glob(evaluation_glob)) +
            # list(glob.glob(evaluation_overflow_glob)))
    return [os.path.join(REPOSITORY_ROOT, path) for path in  MANUAL_EVALUATION]


def run_benchmarks():
    benchmarks = get_benchmarks()
    print('\n'.join(benchmarks), len(benchmarks))
    with open(LOG_FILE, 'a') as fp:
        writer = csv.writer(fp)
        for benchmark in benchmarks:
            if 'overflow' in benchmark:
                check_overflow = 'true'
            else:
                check_overflow = 'false'
            create_configuration_file(check_overflow)
            for i in range(3):
                row = run_benchmark(benchmark)
                if row:
                    writer.writerow(tuple(row) + ('overflow='+check_overflow,))


def run_benchmark(file_path):
    timestamp = datetime.datetime.now().strftime("%y-%m-%d %H:%M:%S")
    print(timestamp, file_path)
    start_time = time.time()
    cmd = [
        "target/release/prusti-rustc",
        file_path,
    ] + MAKE_FLAGS
    print(' '.join(cmd))
    check_exit_status = 'verify/fail' not in file_path
    result = subprocess.run(
        cmd,
        cwd=REPOSITORY_ROOT,
        check=check_exit_status,
        stderr=subprocess.PIPE,
        env=ENV_VARS,
    )
    end_time = time.time()
    duration = end_time - start_time
    match = re.search(
        b'^ INFO .+: prusti_viper::verifier: Verification complete \((.+) seconds\)$',
        result.stderr,
        re.MULTILINE)
    verification_time = float(match.group(1))
    return (timestamp, file_path, start_time, end_time, duration,
            verification_time, str(MAKE_FLAGS), str(ENV_VARS))

def main():
    #build_project()
    run_benchmarks()


if __name__ == '__main__':
    main()
