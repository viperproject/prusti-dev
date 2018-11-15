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
TOML_FILE = os.path.join(ROOT, 'Prusti.toml')
LOG_FILE = os.path.join(ROOT, 'bench.csv')
MAKE_FLAGS = ["JAVA_HOME=/usr/lib/jvm/jdk-11.0.1/"]
ENV_VARS = dict(os.environ,
    Z3_PATH='/home/software/z3/z3-4.8.3.74db2f250907-x64-ubuntu-14.04/bin/z3',
)


def create_configuration_file():
    with open(TOML_FILE, 'w') as fp:
        fp.write(
'''
DUMP_DEBUG_INFO = false
DUMP_BORROWCK_INFO = false
CHECK_BINARY_OPERATIONS = false
''')


def build_project():
    cmd = [
            "make",
            "clean",
            ] + MAKE_FLAGS
    print(' '.join(cmd))
    subprocess.run(
        cmd,
        cwd=ROOT,
        check=True,
        env=ENV_VARS,
    )
    subprocess.run(
        [
            "make",
            "build_release",
            ] + MAKE_FLAGS,
        cwd=ROOT,
        check=True,
        env=ENV_VARS,
    )


def get_benchmarks():
    rosetta_path = os.path.join(ROOT, 'tests/verify/pass/rosetta/')
    rosetta_glob = os.path.join(rosetta_path, '*.rs')
    rosetta_todo_glob = os.path.join(rosetta_path, 'todo', '*.rs')
    rosetta_stress_path = os.path.join(ROOT, 'prusti/tests/verify/todo/stress/rosetta/')
    rosetta_stress_glob = os.path.join(rosetta_stress_path, '*.rs')
    paper_path = os.path.join(ROOT, 'prusti/tests/verify/pass/paper-examples/')
    paper_glob = os.path.join(paper_path, '*.rs')
    return (list(glob.glob(rosetta_glob)) +
            list(glob.glob(rosetta_todo_glob)) +
            list(glob.glob(rosetta_stress_glob)) +
            list(glob.glob(paper_glob)))


def run_benchmarks():
    benchmarks = get_benchmarks()
    with open(LOG_FILE, 'a') as fp:
        writer = csv.writer(fp)
        for benchmark in benchmarks:
            for i in range(3):
                row = run_benchmark(benchmark)
                if row:
                    writer.writerow(row)


def run_benchmark(file_path):
    timestamp = datetime.datetime.now().strftime("%y-%m-%d %H:%M:%S")
    print(timestamp, file_path)
    start_time = time.time()
    result = subprocess.run(
        [
            "make", "run_release",
            "LOG_LEVEL=prusti_viper=info",
            "RUN_FILE=" + file_path,
            ] + MAKE_FLAGS,
        cwd=ROOT,
        check=True,
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
    create_configuration_file()
    build_project()
    run_benchmarks()


if __name__ == '__main__':
    main()
