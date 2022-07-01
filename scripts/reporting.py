"""Helper functions used by `x.py` for error reporting."""

import sys
import traceback


verbose = False


def report(template, *args, **kwargs):
    """Print the message if `verbose` is `True`."""
    if verbose:
        print(template.format(*args, **kwargs))


def error(template, *args, **kwargs):
    """Print the error and exit the program."""
    print(template.format(*args, **kwargs))
    sys.exit(1)


def ensure(condition, err_msg):
    """If `condition` is `False`, print `err_msg` along with a stacktrace, and abort"""
    if not condition:
        traceback.print_stack()
        error(err_msg)
