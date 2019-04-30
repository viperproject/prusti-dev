#!/usr/bin/python3

import json
import glob
import os
import sys
import subprocess


ROOT = os.path.abspath('.')
RUST_VERSION_PATH = os.path.join(ROOT, '../../rust-toolchain')
ROSETTA_PATH = os.path.join(ROOT, 'rosetta')
TASKS_PATH = os.path.join(ROSETTA_PATH, 'tasks.json')
ROSETTA_ANALYSE_SCRIPT = os.path.join(ROSETTA_PATH, 'analyse.sh')
CARGO_BUILD_SCRIPT=os.path.join(ROOT, 'script', 'cargo-build.sh')


def check_json():
    with open(TASKS_PATH) as fp:
        tasks = json.load(fp)
    print(len(tasks))
    for task in tasks:
        print(list(task.keys()))
        code = task['local_code'] or task['remote_code']
        # if code:
            # print(code)
        break

def main(working_dir):
    with open(RUST_VERSION_PATH, "r") as fp:
        rust_version = f.read().strip()
    working_dir = os.path.abspath(working_dir)
    rosetta_repo_local = os.path.join(working_dir, 'rust-rosetta')
    if not os.path.exists(rosetta_repo_local):
        subprocess.run(
            [
                'git',
                'clone',
                'https://github.com/Hoverbear/rust-rosetta.git',
                rosetta_repo_local,
            ],
            cwd=working_dir,
            check=True)

    with open(ROSETTA_ANALYSE_SCRIPT, 'w') as fp:
        def write(s, *args, **kwargs):
            fp.write(s.format(*args, **kwargs))
        write("#!/bin/bash\n")
        write("\n")
        write("rustup toolchain install {}\n".format(rust_version))
        write("rustup default {}\n".format(rust_version))
        write("cargo build\n")
        write("\n")
        write("rm -f '{}/Cargo.toml'\n", rosetta_repo_local)
        write("\n")

        tasks_path = os.path.join(rosetta_repo_local, 'tasks')
        for root, dirs, files in os.walk(tasks_path):
            if 'Cargo.toml' in files:
                write("# {}/Cargo.toml\n", root)
                write("cd '{}'\n", root)
                write("cargo clean\n")
                write("bash '{}'\n", CARGO_BUILD_SCRIPT)
                write("\n")


if __name__ == '__main__':
    main(sys.argv[1])
