#!/usr/bin/python3

import argparse
import os
import glob
from pathlib import Path
import csv
import subprocess
import json
import datetime

def is_test_ignored(file_path):
    for line in open(file_path):
        if 'IgnoreFile(/silicon' in line:
            return True
        if 'IgnoreFile(/Silicon' in line:
            return True
        if 'IgnoreFile(/silver' in line:
            return True
        if 'IgnoreFile(/Silver' in line:
            return True
    return False

class Test:

    def __init__(self, identifier, file_path):
        self.identifier = identifier
        self.file_path = file_path
        self.is_ignored = is_test_ignored(file_path)
        self.args = None
        self.result = None
        self.stdout = None
        self.stderr = None
        self.start_time = None
        self.end_time = None
        self.duration = None
        self.algorithms = []
        self.wands = []
        self.log_files = []
        self.trace_files = []
        self.event_kinds = []
        self.smt2_events = []

    def into_row(self):
        return [
            self.file_path,
            self.is_ignored,
            self.args,
            self.result,
            self.stdout,
            self.stderr,
            self.algorithms,
            self.wands,
        ]

    def into_dict(self):
        return {
            'identifier': self.identifier,
            'file_path': str(self.file_path),
            'is_ignored': self.is_ignored,
            'args': self.args,
            'result': self.result,
            'stdout': self.stdout,
            'stderr': self.stderr,
            'start_time': str(self.start_time) if self.start_time else None,
            'end_time': str(self.end_time) if self.end_time else None,
            'duration': self.duration.total_seconds() if self.duration else None,
            'algorithms': self.algorithms,
            'wands': self.wands,
            'log_files': self.log_files,
            'trace_files': self.trace_files,
            'event_kinds': self.event_kinds,
            'smt2_events': self.smt2_events,
        }

    def execute(
            self,
            viper_server_jar,
            z3_exe,
            temp_directory,
            silicon_flags,
        ):
        """
        java
            -Xss1024m -Xmx4024m \\
            -cp viper_tools/backends/viperserver.jar \\
            viper.silicon.SiliconRunner \\
            --z3Exe z3-4.8.7-x64-ubuntu-16.04/bin/z3 \\
            --numberOfParallelVerifiers=1 \\
            --logLevel TRACE \\
            --tempDirectory log/viper_tmp/deadlock \\
            --maskHeapMode \\
            file
        """
        args = [
            'java',
            '-Xss1024m',
            '-Xmx4024m',
            '-cp', viper_server_jar,
            'viper.silicon.SiliconRunner',
            '--z3Exe', z3_exe,
            '--numberOfParallelVerifiers=1',
            '--logLevel', 'TRACE',
            '--enableTempDirectory',
            '--tempDirectory', temp_directory,
        ] + silicon_flags + [self.file_path]
        self.args = ' '.join(str(arg) for arg in args)
        try:
            self.stdout = os.path.join(temp_directory, 'stdout')
            self.stderr = os.path.join(temp_directory, 'stderr')
            stdout = open(self.stdout, 'w')
            stderr = open(self.stderr, 'w')
            self.start_time = datetime.datetime.now()
            result = subprocess.run(
                args,
                timeout=120,
                stdout=stdout,
                stderr=stderr,
            )
            self.end_time = datetime.datetime.now()
            self.duration = self.end_time - self.start_time
        except subprocess.TimeoutExpired:
            self.result = 'timeout'
        if result.returncode == 0:
            self.result = 'success'
        else:
            self.result = 'failure'

    def analyze_log(self):
        with open(self.stdout) as fp:
            for line in fp:
                if ' - Predicate ' in line:
                    suffix = line.split(' - Predicate ')[1].strip()
                    (predicate, algorithm) = suffix.split(' algorithm ')
                    self.algorithms.append((predicate, algorithm))
                if ' - Field ' in line:
                    suffix = line.split(' - Field ')[1].strip()
                    (predicate, algorithm) = suffix.split(' algorithm ')
                    self.algorithms.append((predicate, algorithm))
                if ' - Quantified wands: ' in line:
                    wands_count = line.split(' - Quantified wands: ')[1]
                    self.wands.append(int(wands_count))

    def count_push_pop_operations(self, temp_directory):
        for log_file in sorted(glob.glob(os.path.join(temp_directory, 'logfile-*.smt2'))):
            push_count = 0
            pop_count = 0
            with open(log_file) as fp:
                for line in fp:
                    if line.startswith('(push) ;'):
                        push_count += 1
                    if line.startswith('(pop) ;'):
                        pop_count += 1
                self.smt2_events.append({
                    'push': push_count,
                    'pop': pop_count,
                })

    def generate_z3_traces(self, z3_exe, temp_directory):
        for log_file in sorted(glob.glob(os.path.join(temp_directory, 'logfile-*.smt2'))):
            self.log_files.append(log_file)
            trace_file = log_file.replace('.smt2', '.trace')
            self.trace_files.append(trace_file)
            self.run_z3(z3_exe, log_file, trace_file)
            assert os.path.exists(trace_file)

    def run_z3(self, z3_exe, log_file, trace_file):
        args = [
            z3_exe,
            'trace=true',
            'proof=true',
            'trace-file-name=' + trace_file,
            log_file,
        ]
        subprocess.run(
            args,
            timeout=600,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

    def parce_z3_traces(self):
        if os.path.exists('target/release/smt-log-analyzer'):
            analyzer = 'target/release/smt-log-analyzer'
        elif os.path.exists('target/debug/smt-log-analyzer'):
            analyzer = 'target/debug/smt-log-analyzer'
        else:
            raise Exception('not found smt-log-analyzer')
        for trace_file in self.trace_files:
            args = [
                analyzer,
                trace_file,
            ]
            subprocess.run(
                args,
                timeout=120,
                check=True,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
            self.parse_event_kinds(trace_file)

    def parse_event_kinds(self, trace_file):
            event_kinds = []
            with open(trace_file + '.event-kinds.csv') as fp:
                for line in fp:
                    (event, count) = line.strip().split(',')
                    if event == 'Event Kind':
                        continue
                    event_kinds.append((event, int(count)))
            self.event_kinds.append(event_kinds)

def collect_tests(viper_tests_path):
    print(viper_tests_path, flush=True)
    tests = []
    for file_path in Path(viper_tests_path).rglob('*.vpr'):
        test = Test(len(tests), file_path)
        tests.append(test)
    return tests

def write_report_csv(tests, report_path):
    with open(report_path, 'w') as fp:
        writer = csv.writer(fp)
        writer.writerow([
            'File',
            'Ignored',
            'Command',
            'Result',
            'Stdout',
            'Stderr',
            'Algorithms',
            'Wands',
        ])
        for test in tests:
            writer.writerow(test.into_row())

def write_report_json(tests, report_path):
    with open(report_path, 'w') as fp:
        json.dump([test.into_dict() for test in tests], fp, sort_keys=True, indent=4)

def execute_tests(
        tests,
        workspace,
        viper_server_jar,
        z3_exe,
        silicon_flags,
    ):
    for test in tests:
        if not test.is_ignored:
            print(test.file_path, datetime.datetime.now(), flush=True)
            try:
                temp_directory = os.path.join(workspace, f'test-{test.identifier:04}')
                os.mkdir(temp_directory)
                test.execute(
                    viper_server_jar,
                    z3_exe,
                    temp_directory,
                    silicon_flags,
                )
                test.analyze_log()
                test.count_push_pop_operations(temp_directory)
                test.generate_z3_traces(z3_exe, temp_directory)
                test.parce_z3_traces()  # Call Rust SMT analyzer and use its CSV.
            except Exception as e:
                print(e)

def analyze_test_results(workspace):
    tests = []
    for directory in os.listdir(workspace):
        if not directory.startswith('test-'):
            continue
        temp_directory = os.path.join(workspace, directory)
        log_file = os.path.join(temp_directory, 'logfile-00.smt2')
        if not os.path.exists(log_file):
            continue
        file_path = None
        with open(log_file) as fp:
            for line in fp:
                if line.startswith('; Input file:'):
                    file_path = line.split('; Input file:')[1].strip()
                    break
        if file_path is None:
            continue
        identifier = int(directory.split('-')[1])
        test = Test(identifier, file_path)
        tests.append(test)
        test.stdout = os.path.join(temp_directory, 'stdout')
        test.stderr = os.path.join(temp_directory, 'stderr')
        test.analyze_log()
        test.log_files = list(sorted(glob.glob(os.path.join(temp_directory, 'logfile-*.smt2'))))
        test.trace_files = list(sorted(glob.glob(os.path.join(temp_directory, 'logfile-*.trace'))))
        for trace_file in test.trace_files:
            try:
                test.parse_event_kinds(trace_file)
            except Exception as e:
                print(e)
    return tests

def parse_args():
    parser = argparse.ArgumentParser(description="Benchmark Silicon Z3 statistics.")
    parser.add_argument(
        "--viper-server-jar",
        help="path of the Viper server JAR",
        default='viper_tools/backends/viperserver_meilers_silicarbon.jar',
    )
    parser.add_argument(
        "--z3-exe",
        help="path to Z3",
        default='viper_tools/z3/bin/z3',
    )
    parser.add_argument(
        "--viper-tests",
        help="path to Viper tests folder",
        default='../viperserver/silicon/silver/src/test/resources/',
    )
    parser.add_argument(
        "--report-csv",
        help="output path of the CSV file",
        default='../workspace/report.csv',
    )
    parser.add_argument(
        "--report-json",
        help="output path of the JSON file",
        default='../workspace/report.json',
    )
    parser.add_argument(
        "--workspace",
        help="the workspace directory",
        default='../workspace',
    )
    return parser.parse_args()

def main():
    args = parse_args()
    if not os.path.exists(args.workspace):
        tests = collect_tests(args.viper_tests)
        os.mkdir(args.workspace)
        try:
            execute_tests(
                tests,
                args.workspace,
                args.viper_server_jar,
                args.z3_exe,
                [], #['--maskHeapMode'],
            )
        finally:
            write_report_csv(tests, args.report_csv)
            write_report_json(tests, args.report_json)
    else:
        tests = analyze_test_results(args.workspace)
        write_report_csv(tests, args.report_csv)
        write_report_json(tests, args.report_json)

if __name__ == '__main__':
    main()

