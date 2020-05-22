#!/usr/bin/python3

import sys
import subprocess
import os

def run(*args, **kwargs):
    res = subprocess.run(*args, **kwargs, stdout=subprocess.PIPE)
    return res.stdout

def find_smallvec():
    toolchain = open('rust-toolchain').read().strip()
    sysroot = run(['rustup', 'run', toolchain, 'rustc', '--print', 'sysroot']).strip()
    libs = run(['find', sysroot, '-name', '*smallvec*']).strip().splitlines()
    for lib in libs:
        strings = run(['strings', lib])
        if b'smallvec-1.4' in strings:
            return lib.decode('utf-8')
    raise Exception("Could not found smallvec")

def main(args):
    smallvec = find_smallvec()
    env = os.environ.copy()
    rustflags = '--extern my_smallvec=' + smallvec
    print('export RUSTFLAGS="{}"'.format(rustflags))
    env['RUSTFLAGS'] = rustflags
    subprocess.run(['cargo'] + args[1:], env = env)


if __name__ == '__main__':
    main(sys.argv)
