#!/usr/bin/python3

"""A wrapper for cargo that sets up the Prusti environment."""

import os
import platform
import subprocess
import sys

verbose = False
dry_run = False


def default_linux_java_loc():
    if os.path.exists('/usr/lib/jvm/default-java'):
        return '/usr/lib/jvm/default-java'
    elif os.path.exists('/usr/lib/jvm/default'):
        return '/usr/lib/jvm/default'
    report("Could not determine default java location.")


def report(template, *args, **kwargs):
    """Print the message if `verbose` is `True`."""
    if verbose:
        print(template.format(*args, **kwargs))


def error(template, *args, **kwargs):
    """Print the error and exit the program."""
    print(template.format(*args, **kwargs))
    sys.exit(1)


def get_var_or(name, default):
    """If environment variable `name` set, return its value or `default`."""
    if name in os.environ:
        return os.environ[name]
    else:
        return default


def get_linux_env():
    """Get environment variables for Linux."""
    java_home = get_var_or('JAVA_HOME', default_linux_java_loc())
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
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/backends'))
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    return variables


def get_mac_env():
    """Get environment variables for Mac."""
    java_home = get_var_or('JAVA_HOME', None)
    if java_home is None:
        java_home = subprocess.run(["/usr/libexec/java_home"], stdout=subprocess.PIPE).stdout.strip()
    variables = [
        ('JAVA_HOME', java_home),
        ('RUST_TEST_THREADS', '1'),
    ]
    if os.path.exists(java_home):
        ld_library_path = None
        for root, _, files in os.walk(java_home):
            if 'libjvm.dylib' in files:
                ld_library_path = root
                break
        if ld_library_path is None:
            report("could not find libjvm.dylib in {}", java_home)
        else:
            variables.append(('LD_LIBRARY_PATH', ld_library_path))
            variables.append(('DYLD_LIBRARY_PATH', ld_library_path))
    viper_home = get_var_or('VIPER_HOME', os.path.abspath('viper_tools/backends'))
    if os.path.exists(viper_home):
        variables.append(('VIPER_HOME', viper_home))
    z3_exe = os.path.abspath(os.path.join(viper_home, '../z3/bin/z3'))
    if os.path.exists(z3_exe):
        variables.append(('Z3_EXE', z3_exe))
    return variables


def set_env_variables(env, variables):
    """Set the given environment variables in `env` if not already set."""
    for name, value in variables:
        if name not in env:
            env[name] = value
        report("env: {}={}", name, env[name])


def get_env():
    """Returns the environment with the variables set."""
    env = os.environ.copy()
    if sys.platform == "linux" or sys.platform == "linux2":
        # Linux
        set_env_variables(env, get_linux_env())
    elif sys.platform == "darwin":
        # Mac
        set_env_variables(env, get_mac_env())
    else:
        error("unsupported platform: {}", sys.platform)
    return env


def run_command(args):
    """Run a command with the given arguments."""
    completed = subprocess.run(args, env=get_env())
    if completed.returncode != 0:
        sys.exit(completed.returncode)


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


def setup_ubuntu():
    """Install the dependencies on Ubuntu."""
    # Install dependencies.
    shell('sudo apt-get update')
    shell('sudo apt-get install -y '
          'build-essential pkg-config '
          'wget gcc libssl-dev openjdk-8-jdk')
    # Download Viper.
    shell('wget -q http://viper.ethz.ch/downloads/ViperToolsNightlyLinux.zip')
    shell('unzip ViperToolsNightlyLinux.zip -d viper_tools')
    shell('rm ViperToolsNightlyLinux.zip')


def setup_linux():
    """Install the dependencies on generic Linux."""
    shell('curl http://viper.ethz.ch/downloads/ViperToolsNightlyLinux.zip -o ViperToolsNightlyLinux.zip')
    shell('unzip ViperToolsNightlyLinux.zip -d viper_tools')
    shell('rm ViperToolsNightlyLinux.zip')


def setup_mac():
    """Install the dependencies on Mac."""
    # Non-Viper dependencies must be installed manually.
    # Download Viper.
    shell('curl http://viper.ethz.ch/downloads/ViperToolsNightlyMac.zip -o ViperToolsNightlyMac.zip')
    shell('unzip ViperToolsNightlyMac.zip -d viper_tools')
    shell('rm ViperToolsNightlyMac.zip')


def setup_rustup():
    # Setup rustc components.
    shell('rustup component add rustfmt', term_on_nzec=False)
    shell('rustup component add rust-src')
    shell('rustup component add rustc-dev')
    shell('rustup component add llvm-tools-preview')


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
        if sys.platform == "linux" or sys.platform == "linux2":
            if 'Ubuntu' in platform.platform():
                setup_ubuntu()
            else:
                setup_linux()
        elif sys.platform == "darwin":
            setup_mac()
        else:
            error("unsupported platform: {}", sys.platform)
    setup_rustup()


def ide(args):
    """Start VS Code with the given arguments."""
    run_command(['code'] + args)


def main(argv):
    global verbose
    args = []
    for i, arg in enumerate(argv):
        if arg.startswith('+'):
            if arg == '+v' or arg == '++verbose':
                verbose = True
                continue
            else:
                error('unknown option: {}', arg)
        elif arg == 'setup':
            setup(argv[i+1:])
            break
        elif arg == 'ide':
            ide(argv[i+1:])
            break
        else:
            cargo(argv[i:])
            break
    if not argv:
        cargo(argv)


if __name__ == '__main__':
    main(sys.argv[1:])
