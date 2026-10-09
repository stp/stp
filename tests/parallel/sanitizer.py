"""Sanitizer builds. CMake sets STPP_SANITIZED=1 for the label's scripts when
the build is instrumented by an address, thread or memory sanitizer, whose
shadow memory does not fit under an address-space limit: every stp-p and
stpp-drive run then gets --worker-memory-mib 0 unless it sets its own, and
a script can set the sanitizers' runtime reports aside before it compares
stderr. In any other build nothing changes."""
import os
import subprocess

ON = os.environ.get('STPP_SANITIZED') == '1'


def flags():
    """What a command line of stp-p or stpp-drive gets in this build."""
    return ['--worker-memory-mib', '0'] if ON else []


def install(*executables):
    """Every subprocess.Popen (and so subprocess.run) of one of `executables`
    gets flags(), unless its command line sets --worker-memory-mib."""
    if not ON:
        return
    names = {str(e) for e in executables}
    base = subprocess.Popen

    class Popen(base):
        def __init__(self, args, *rest, **kwargs):
            if (isinstance(args, (list, tuple)) and args and str(args[0]) in names
                    and '--worker-memory-mib' not in args):
                args = [args[0], *flags(), *args[1:]]
            super().__init__(args, *rest, **kwargs)

    subprocess.Popen = Popen


def stderr(text):
    """stderr without the sanitizers' runtime reports."""
    if not ON or not isinstance(text, str):
        return text
    return ''.join(line for line in text.splitlines(True)
                   if 'runtime error:' not in line and not line.startswith('SUMMARY: '))
