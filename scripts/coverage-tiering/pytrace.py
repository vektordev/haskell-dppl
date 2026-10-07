"""Line coverage of the NeST Python runtimes, for coverage_tiering.py.

The test suite runs emitted Python as ``python3 <script>`` (or ``-c <code>``).
coverage_tiering.py puts a ``python3`` shim on PATH (and points
NEST_TORCH_PYTHON at a second one) that runs ``<real python> pytrace.py
<original args>``. This file then runs the original program unchanged and, at
exit, appends the lines it executed in ``pythonLib.py`` / ``pythonLibBatched.py``
to ``$NEST_COV_DIR/py-<pid>.txt`` as ``<file>:<line>`` rows.

It uses ``sys.monitoring`` (Python >= 3.12): LINE events are disabled for every
code object outside the two runtime files, so the overhead elsewhere is one
event per code object. coverage.py is not installed on the analysis machine;
this needs only the standard library.
"""
import atexit
import os
import runpy
import sys

TARGETS = {"pythonLib.py", "pythonLibBatched.py"}
hits = set()


def _line(code, line):
    name = os.path.basename(code.co_filename)
    if name in TARGETS:
        hits.add((name, line))
        return None
    return sys.monitoring.DISABLE


def _dump():
    out = os.environ.get("NEST_COV_DIR")
    if not out or not hits:
        return
    path = os.path.join(out, "py-%d.txt" % os.getpid())
    with open(path, "a") as f:
        for name, line in sorted(hits):
            f.write("%s:%d\n" % (name, line))


def main():
    mon = sys.monitoring
    tool = mon.COVERAGE_ID
    mon.use_tool_id(tool, "nest-pytrace")
    mon.register_callback(tool, mon.events.LINE, _line)
    mon.set_events(tool, mon.events.LINE)
    atexit.register(_dump)

    args = sys.argv[1:]
    if args and args[0] == "-c":
        code = args[1]
        sys.argv = ["-c"] + args[2:]
        sys.path.insert(0, "")
        exec(compile(code, "<string>", "exec"), {"__name__": "__main__"})
    elif not args or args[0] == "-":
        code = sys.stdin.read()
        sys.argv = ["-"] + args[1:]
        sys.path.insert(0, "")
        exec(compile(code, "<stdin>", "exec"), {"__name__": "__main__"})
    else:
        script = args[0]
        sys.argv = args
        sys.path[0] = os.path.dirname(os.path.abspath(script))
        runpy.run_path(script, run_name="__main__")


if __name__ == "__main__":
    main()
