"""Helper functions used by `x.py`."""

import datetime
import os
import sys
import subprocess
from reporting import (
    ensure, report
)


JAVA_NOT_FOUND_ERR_MSG = """Could not detect a Java installation.
If Java is already installed, you can fix this by setting the JAVA_HOME environment variable."""


def default_linux_java_loc():
    if os.path.exists('/usr/lib/jvm/default-java'):
        return '/usr/lib/jvm/default-java'
    elif os.path.exists('/usr/lib/jvm/default'):
        return '/usr/lib/jvm/default'
    elif os.path.exists('/usr/local/sdkman/candidates/java/current'):
        return '/usr/local/sdkman/candidates/java/current'
    report("Could not determine default java location.")


def get_env():
    """Returns the environment with the variables set."""
    env = os.environ.copy()
    if sys.platform in ("linux", "linux2"):
        # Linux
        set_env_variables(env, get_linux_env())
    elif sys.platform == "darwin":
        # Mac
        set_env_variables(env, get_mac_env())
    elif sys.platform == "win32":
        # Windows
        set_env_variables(env, get_win_env())
    else:
        error("unsupported platform: {}", sys.platform)
    return env


def set_env_variables(env, variables):
    """Set the given environment variables in `env` if not already set, merging special variables."""
    for name, value in variables:
        if name not in env:
            env[name] = value
        elif name in ("PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"):
            if sys.platform == "win32":
                env[name] += ";" + value
            else:
                env[name] += ":" + value
        report("env: {}={}", name, env[name])


def get_linux_env():
    """Get environment variables for Linux."""
    java_home = get_var_or('JAVA_HOME', default_linux_java_loc())
    ensure(java_home is not None, JAVA_NOT_FOUND_ERR_MSG)
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        ld_library_path = None
        for root, _, files in os.walk(java_home):
            if 'libjvm.so' in files:
                ld_library_path = root
                break
        if ld_library_path is None:
            report("could not find libjvm.so in {}", java_home)
        else:
            variables.append(('LD_LIBRARY_PATH', ld_library_path))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/server'))
    if not os.path.exists(viper_home):
        viper_home = os.path.abspath('viper_tools/backends')
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    boogie_exe = os.path.abspath(os.path.join(viper_home, '../boogie/Binaries/Boogie'))
    if os.path.exists(boogie_exe):
        variables.append(('BOOGIE_EXE', boogie_exe))
    return variables


def get_mac_env():
    """Get environment variables for Mac."""
    java_home = get_var_or('JAVA_HOME', None)
    if java_home is None:
        java_home = subprocess.run(["/usr/libexec/java_home"], stdout=subprocess.PIPE, encoding="utf8").stdout.strip()
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        ld_library_path = None
        for root, _, files in os.walk(java_home):
            if 'libjli.dylib' in files:
                ld_library_path = root
                break
        if ld_library_path is None:
            report("could not find libjli.dylib in {}", java_home)
        else:
            variables.append(('LD_LIBRARY_PATH', ld_library_path))
            variables.append(('DYLD_LIBRARY_PATH', ld_library_path))
    else:
        error(JAVA_NOT_FOUND_ERR_MSG)
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/server'))
    if not os.path.exists(viper_home):
        viper_home = os.path.abspath('viper_tools/backends')
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    boogie_exe = os.path.abspath(os.path.join(viper_home, '../boogie/Binaries/Boogie'))
    if os.path.exists(boogie_exe):
        variables.append(('BOOGIE_EXE', boogie_exe))
    return variables


def get_win_env():
    """Get environment variables for Windows."""
    java_home = get_var_or('JAVA_HOME', None)
    ensure(java_home is not None, JAVA_NOT_FOUND_ERR_MSG)
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        library_path = None
        for root, _, files in os.walk(java_home):
            if 'jvm.dll' in files:
                library_path = root
                break
        if library_path is None:
            report("could not find jvm.dll in {}", java_home)
        else:
            variables.append(('PATH', library_path))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath(os.path.join('viper_tools', 'server')))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath(os.path.join('viper_tools', 'server')))
    if not os.path.exists(viper_home):
        viper_home = get_var_or('VIPER_HOME', os.path.abspath(os.path.join('viper_tools', 'backends')))
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    else:
        report("could not find VIPER_HOME in {}", viper_home)
    z3_exe = os.path.abspath(os.path.join(viper_home, os.path.join('..', 'z3', 'bin', 'z3.exe')))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    boogie_exe = os.path.abspath(os.path.join(viper_home, '..', 'boogie', 'Binaries', 'Boogie'))
    if os.path.exists(boogie_exe):
        variables.append(('BOOGIE_EXE', boogie_exe))
    return variables


def get_var_or(name, default):
    """If environment variable `name` set, return its value or `default`."""
    if name in os.environ:
        return os.environ[name]
    else:
        return default


def run_command(args, env=None, cwd=None, on_exit=None, report_time=False):
    """Run a command with the given arguments.

    +   ``env`` – an environment in which to run.
    +   ``cwd`` – the path at which to run.
    +   ``on_exit`` – function to be executed on exit.
    +   ``report_time`` – whether to report how long it took to execute
        the command.
    """
    if env is None:
        env = get_env()
    start_time = datetime.datetime.now()
    completed = subprocess.run(args, env=env, cwd=cwd)
    if report_time:
        print(datetime.datetime.now() - start_time)
    if on_exit is not None:
        on_exit()
    if completed.returncode != 0:
        sys.exit(completed.returncode)


def extract_test_compile_flags(test_path):
    compile_flags = []
    with open(test_path) as fp:
        for line in fp:
            if line.startswith('// compile-flags:'):
                compile_flags.extend(line[len('// compile-flags:'):].strip().split())
        report("Additional compile flags: {}", compile_flags)
    return compile_flags
