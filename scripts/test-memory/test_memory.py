#!/usr/bin/env python3
"""Per-group and per-test memory of the test suite: who drives the peak.

Offline tool, not part of ``stack test`` (docs-repo investigation
``slow-tier-run-killed-for-low-memory``; docs/testing.md, "Test suite
memory"). It answers two questions about a test binary that grows too large:

  groups  Which test group drives the peak? Runs every unit (a test group at
          ``--depth``) in its own process, each in a transient systemd unit
          under a hard memory cap (``MemoryMax``, no swap), so a runaway unit
          is OOM-killed alone instead of taking the machine down. Records the
          cgroup's memory peak (the test binary *and* its python/julia/nest
          children), GHC's own figures from ``+RTS -t`` (maximum residency,
          heap in use, bytes allocated), wall time and the outcome (ok,
          failed, oom-kill). Writes ``groups.csv`` and each unit's output under
          ``logs/``, and prints the units by peak.
  trace   Which test inside a group? Runs one selection at ``-j1`` in one
          process (the tree is built once), samples the cgroup's anonymous
          memory every ``--interval`` seconds, and attributes it to the test
          tasty was running at that moment (tasty prints a test's name when
          it starts and its result when it ends). Prints the tests by the rise
          they caused (memory at their peak minus memory when they started)
          and writes ``trace.csv``. GHC rarely hands heap back to the OS, so
          a test that runs after a big one is not charged for it: a rise is
          new memory, and the last test before an OOM kill is named.

Both run the binary already built in ``.stack-work`` (``stack build --test
--no-run-tests`` first), from the package root, and pass the environment
through: set ``NEST_SLOW_TESTS=1`` (and ``NEST_FULL_TESTS=1``, or impact
analysis skips most of the work being measured) yourself.

Usage (from anywhere; paths default to this checkout):

  NEST_SLOW_TESTS=1 NEST_FULL_TESTS=1 scripts/test-memory/test_memory.py groups --cap 6G
  NEST_SLOW_TESTS=1 NEST_FULL_TESTS=1 scripts/test-memory/test_memory.py groups --only Slow --depth 3
  NEST_SLOW_TESTS=1 NEST_FULL_TESTS=1 scripts/test-memory/test_memory.py trace -p '/RewriteInvarianceCorpus/'

``--suite haskell-dppl-test-corpus`` measures the corpus binary instead.
Outputs land in ``.stack-work/test-memory/`` (``--out`` to change). Units run
one at a time by default: the point is a clean figure per unit, and parallel
units would share the machine's memory with each other. ``-j`` runs several
anyway, each under its own cap.
"""

import argparse
import csv
import os
import re
import select
import subprocess
import sys
import threading
import time
import uuid

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
MAIN_SUITE = "haskell-dppl-test"


def log(msg):
    print(msg, file=sys.stderr, flush=True)


def stack_path(repo, what):
    return subprocess.run(["stack", "path", what], cwd=repo, capture_output=True,
                          text=True, check=True).stdout.strip()


def binary(repo, suite):
    p = os.path.join(repo, stack_path(repo, "--dist-dir"), "build", suite, suite)
    if not os.path.exists(p):
        sys.exit("missing %s (stack build --test --no-run-tests)" % p)
    return p


def awk_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def prefix_pattern(prefix):
    """A tasty pattern selecting exactly the tests under group path ``prefix``."""
    p = prefix + "."
    return "substr($0, 1, %d) == %s" % (len(p), awk_str(p))


def parse_size(s):
    """systemd's human sizes ("8G", "512.3M", "3.1K", "100B") in bytes."""
    m = re.match(r"^([\d.]+)([BKMGT]?)$", s.strip())
    if not m:
        return None
    mult = {"": 1, "B": 1, "K": 1 << 10, "M": 1 << 20, "G": 1 << 30, "T": 1 << 40}[m.group(2)]
    return int(float(m.group(1)) * mult)


def mb(b):
    return "" if b is None else "%.0f" % (b / (1 << 20))


# --------------------------------------------------------------------------
# Running one selection in a capped transient unit


class Run:
    """The test binary under ``systemd-run --user --wait``, its own cgroup.

    ``systemd-run`` reports the unit's memory peak when it exits, which
    covers every child process, and kills the whole unit at ``MemoryMax``."""

    def __init__(self, a, args, tag, env=None, drain_stdout=True):
        self.unit = "nest-test-memory-%s-%s" % (tag, uuid.uuid4().hex[:8])
        self.rts = os.path.join(a.out, "%s.rts" % self.unit)
        # Not --quiet: the resource summary systemd-run prints to stderr on
        # exit is where the unit's memory peak and result come from.
        cmd = ["systemd-run", "--user", "--wait", "--pipe", "--unit", self.unit,
               "--working-directory", a.repo, "-p", "MemoryMax=" + a.cap, "-p", "MemorySwapMax=0"]
        passed = {k: v for k, v in os.environ.items()
                  if k.startswith(("NEST_", "TASTY_")) or k in ("PATH", "HOME", "LANG", "LC_ALL")}
        # `stack test` puts the build-tools (haskell-dppl-exe, for TestCLI)
        # on PATH; so does this.
        passed["PATH"] = a.exe_dir + os.pathsep + passed.get("PATH", "")
        passed.update(env or {})
        for k, v in passed.items():
            cmd += ["-E", "%s=%s" % (k, v)]
        # systemd expands $VAR in a unit's command line; tasty patterns use $0.
        args = [x.replace("$", "$$") for x in args]
        self.cmd = cmd + [a.binary] + args + ["+RTS", "-t" + self.rts, "--machine-readable", "-RTS"]
        self.start = time.monotonic()
        self.proc = subprocess.Popen(self.cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.stderr = []
        self.stdout = []
        # Drain both pipes as the run goes: a full pipe would block the
        # binary. The trace reads stdout itself, as it arrives.
        self._ts = [threading.Thread(target=self._drain, args=(self.proc.stderr, self.stderr), daemon=True)]
        if drain_stdout:
            self._ts.append(threading.Thread(target=self._drain, args=(self.proc.stdout, self.stdout), daemon=True))
        for t in self._ts:
            t.start()

    @staticmethod
    def _drain(pipe, into):
        for line in pipe:
            into.append(line.decode("utf-8", "replace"))

    def cgroup(self, timeout=10):
        """The unit's cgroup directory, once systemd has created it."""
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            r = subprocess.run(["systemctl", "--user", "show", "-P", "ControlGroup",
                                self.unit + ".service"], capture_output=True, text=True)
            cg = r.stdout.strip()
            if cg and os.path.isdir("/sys/fs/cgroup" + cg):
                return "/sys/fs/cgroup" + cg
            if self.proc.poll() is not None:
                return None
            time.sleep(0.05)
        return None

    def join(self):
        self.proc.wait()
        for t in self._ts:
            t.join()

    def finish(self, stdout_tail):
        self.join()
        wall = time.monotonic() - self.start
        err = "".join(self.stderr)
        res = {"wall_s": "%.1f" % wall, "exit": self.proc.returncode}
        m = re.search(r"Finished with result: (\S+)", err)
        res["result"] = m.group(1) if m else "?"
        m = re.search(r"Memory peak: (\S+)", err)
        res["peak"] = parse_size(m.group(1)) if m else None
        rts = {}
        if os.path.exists(self.rts):
            body = open(self.rts).read()
            rts = dict(re.findall(r'\("([^"]+)", "([^"]*)"\)', body))
            os.remove(self.rts)
        for k in ("max_bytes_used", "max_mem_in_use_bytes", "bytes allocated"):
            res[k] = int(rts[k]) if k in rts else None
        if res["result"] == "oom-kill":
            res["outcome"] = "oom-kill"
        elif res["result"] == "success":
            res["outcome"] = "ok"
        else:
            res["outcome"] = "failed"
        m = re.search(r"(\d+) out of (\d+) tests failed|All (\d+) tests passed", stdout_tail)
        res["summary"] = m.group(0) if m else ""
        return res


# --------------------------------------------------------------------------
# groups


def list_tests(a):
    r = subprocess.run([a.binary, "-l"] + (["-p", a.pattern] if a.pattern else []),
                       cwd=a.repo, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("listing failed:\n" + r.stderr)
    lines = [l for l in r.stdout.splitlines() if l.strip()]
    # A test name may span lines (a program's source as its name); a
    # continuation line does not start with the root group's name.
    root = lines[0].split(".", 1)[0] + "." if lines else ""
    return [l for l in lines if l.startswith(root)]


def units_of(tests, depth, only, split):
    """Group paths ``depth`` components deep (2 is ``Tests.<group>``), one
    level deeper inside a group named in ``split``. A test directly in a
    group is its own unit's member, never a unit of its own."""
    units = {}
    for t in tests:
        parts = t.split(".")
        d = depth
        while d < len(parts) - 1 and parts[d - 1] in split:
            d += 1
        if only and only not in parts[:d]:
            continue
        key = ".".join(parts[:min(d, len(parts) - 1)])
        units.setdefault(key, []).append(t)
    return units


def unit_pattern(unit, members, tests):
    """The group prefix, unless it would also select tests of other units
    (the direct leaves of a split group): then the members by name."""
    if sum(1 for t in tests if t.startswith(unit + ".")) == len(members):
        return prefix_pattern(unit)
    return " || ".join("$0 == " + awk_str(t) for t in members)


def cmd_groups(a):
    tests = list_tests(a)
    units = units_of(tests, a.depth, a.only, set(a.split))
    log("%d tests, %d units at depth %d" % (len(tests), len(units), a.depth))
    os.makedirs(os.path.join(a.out, "logs"), exist_ok=True)
    path = os.path.join(a.out, "groups.csv")
    fields = ["unit", "tests", "outcome", "summary", "peak_mb", "max_residency_mb",
              "heap_in_use_mb", "allocated_mb", "wall_s"]
    rows = []
    pending = sorted(units)
    running = []
    while pending or running:
        while pending and len(running) < a.jobs:
            u = pending.pop(0)
            log("run  %s (%d tests)" % (u, len(units[u])))
            pat = unit_pattern(u, units[u], tests)
            if a.pattern:
                pat = "(%s) && (%s)" % (a.pattern, pat)
            running.append((u, Run(a, ["-p", pat] + a.tasty, "g")))
        for item in list(running):
            u, run = item
            if run.proc.poll() is None:
                continue
            run.join()
            res = run.finish("".join(run.stdout[-200:]))
            out = "".join(run.stdout)
            with open(os.path.join(a.out, "logs", re.sub(r"[^\w.-]+", "_", u) + ".log"), "w") as f:
                f.write(out + "".join(run.stderr))
            running.remove(item)
            row = {"unit": u, "tests": len(units[u]), "outcome": res["outcome"], "summary": res["summary"],
                   "peak_mb": mb(res["peak"]), "max_residency_mb": mb(res["max_bytes_used"]),
                   "heap_in_use_mb": mb(res["max_mem_in_use_bytes"]),
                   "allocated_mb": mb(res["bytes allocated"]), "wall_s": res["wall_s"]}
            rows.append(row)
            log("done %s: %s, peak %s MB, residency %s MB, %s s" % (
                u, row["outcome"], row["peak_mb"], row["max_residency_mb"], row["wall_s"]))
            with open(path, "w", newline="") as f:
                w = csv.DictWriter(f, fieldnames=fields)
                w.writeheader()
                w.writerows(sorted(rows, key=lambda r: r["unit"]))
        time.sleep(0.2)
    rows.sort(key=lambda r: -float(r["peak_mb"] or 0))
    print("%-70s %6s %-9s %8s %9s %8s" % ("unit", "tests", "outcome", "peak MB", "resid MB", "wall s"))
    for r in rows:
        print("%-70s %6s %-9s %8s %9s %8s" % (r["unit"][:70], r["tests"], r["outcome"], r["peak_mb"],
                                            r["max_residency_mb"], r["wall_s"]))
    log("wrote " + path)


# --------------------------------------------------------------------------
# trace

# A leaf as tasty prints it: indentation, the name, a colon, padding. The
# name and padding are printed when the test starts; OK/FAIL when it ends.
LEAF_START = re.compile(r"^( *)(\S.*?):\s+$")
LEAF_END = re.compile(r"^( *)(\S.*?):\s+(OK|FAIL)\b")


def anon_bytes(cg):
    try:
        with open(os.path.join(cg, "memory.stat")) as f:
            for line in f:
                if line.startswith("anon "):
                    return int(line.split()[1])
    except OSError:
        return None
    return None


def cmd_trace(a):
    if not a.pattern:
        sys.exit("trace needs -p PATTERN (one group; the whole suite at -j1 takes hours)")
    # Every test's line is the clock, so successes must be shown.
    run = Run(a, ["-j1", "-p", a.pattern] + a.tasty, "t", {"TASTY_HIDE_SUCCESSES": "false"},
              drain_stdout=False)
    cg = run.cgroup()
    fd = run.proc.stdout.fileno()
    os.set_blocking(fd, False)
    buf = b""
    stack = []          # enclosing group names, by depth (indentation / 2)
    leaf_indent = -1    # indentation of the last leaf; deeper lines are its info
    current = None      # the running test
    tests = []
    log_lines = []
    before_first = 0    # peak while the tree is built, before any test runs
    while True:
        now = time.monotonic()
        m = anon_bytes(cg) if cg else None
        if m is not None and current is not None:
            current["peak"] = max(current["peak"], m)
        elif m is not None and not tests:
            before_first = max(before_first, m)
        r, _, _ = select.select([fd], [], [], a.interval)
        chunk = b""
        if r:
            try:
                chunk = os.read(fd, 65536)
            except BlockingIOError:
                pass
            if not chunk and run.proc.poll() is not None:
                break
        elif run.proc.poll() is not None:
            break
        buf += chunk
        lines = buf.split(b"\n")
        buf = lines.pop()
        complete = [(l.decode("utf-8", "replace"), True) for l in lines]
        if buf:
            complete.append((buf.decode("utf-8", "replace"), False))
        for line, whole in complete:
            if whole:
                log_lines.append(line)
            end = LEAF_END.match(line)
            start = None if end else LEAF_START.match(line)
            leaf = end or start
            if leaf and current is None:
                ind = len(leaf.group(1))
                name = ".".join(stack[:ind // 2] + [leaf.group(2)])
                mem0 = m if m is not None else 0
                current = {"name": name, "start": now, "mem0": mem0, "peak": mem0}
                leaf_indent = ind
            if end and current is not None:
                current["end"] = now
                current["result"] = end.group(3)
                tests.append(current)
                current = None
            elif whole and not leaf and line.strip():
                ind = len(line) - len(line.lstrip(" "))
                if 0 <= leaf_indent < ind:
                    continue        # a finished leaf's info lines
                stack = stack[:ind // 2] + [line.strip()]
                leaf_indent = -1
    res = run.finish("\n".join(log_lines[-50:]))
    if current is not None:
        current["end"] = time.monotonic()
        current["result"] = "KILLED" if res["outcome"] == "oom-kill" else "unfinished"
        tests.append(current)
    path = os.path.join(a.out, "trace.csv")
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["test", "result", "seconds", "anon_at_start_mb", "anon_peak_mb", "rise_mb"])
        for t in tests:
            w.writerow([t["name"], t["result"], "%.2f" % (t["end"] - t["start"]), mb(t["mem0"]),
                        mb(t["peak"]), mb(t["peak"] - t["mem0"])])
    with open(os.path.join(a.out, "trace.log"), "w") as f:
        f.write("\n".join(log_lines) + "\n")
    print("run: %s, cgroup peak %s MB, GHC max residency %s MB, %s MB before the first test" % (
        res["outcome"], mb(res["peak"]), mb(res["max_bytes_used"]), mb(before_first)))
    print("%-80s %-10s %8s %8s %8s" % ("test (by rise)", "result", "seconds", "peak MB", "rise MB"))
    for t in sorted(tests, key=lambda t: -(t["peak"] - t["mem0"]))[:a.top]:
        print("%-80s %-10s %8.1f %8s %8s" % (t["name"][-80:], t["result"], t["end"] - t["start"],
                                           mb(t["peak"]), mb(t["peak"] - t["mem0"])))
    log("wrote %s and trace.log (%d tests)" % (path, len(tests)))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--repo", default=REPO)
    ap.add_argument("--suite", default=MAIN_SUITE, help="test binary (default %(default)s)")
    ap.add_argument("--out", default=None, help="output dir (default .stack-work/test-memory)")
    ap.add_argument("--cap", default="6G", help="MemoryMax per run (default %(default)s)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("groups", help="one capped process per test group")
    g.add_argument("--depth", type=int, default=2,
                   help="group depth of a unit: 2 is Tests.<group> (default %(default)s)")
    g.add_argument("--split", action="append", default=None,
                   help="a group to split one level deeper (repeatable; default: Slow)")
    g.add_argument("--only", default=None, help="only units with this path component (e.g. Slow)")
    g.add_argument("-p", dest="pattern", default=None, help="tasty pattern restricting the listing")
    g.add_argument("-j", dest="jobs", type=int, default=1, help="units run at once (default 1)")
    t = sub.add_parser("trace", help="per-test memory within one selection, at -j1")
    t.add_argument("-p", dest="pattern", required=True, help="tasty pattern selecting the tests")
    t.add_argument("--interval", type=float, default=0.2, help="sampling period in seconds")
    t.add_argument("--top", type=int, default=25, help="tests printed (default %(default)s)")
    for sp in (g, t):
        sp.add_argument("tasty", nargs="*", help="further tasty arguments, after --")
    a = ap.parse_args()
    if a.cmd == "groups" and a.split is None:
        a.split = ["Slow"]
    a.repo = os.path.abspath(a.repo)
    a.binary = binary(a.repo, a.suite)
    a.exe_dir = os.path.join(stack_path(a.repo, "--local-install-root"), "bin")
    a.out = os.path.abspath(a.out or os.path.join(a.repo, ".stack-work", "test-memory"))
    os.makedirs(a.out, exist_ok=True)
    {"groups": cmd_groups, "trace": cmd_trace}[a.cmd](a)


if __name__ == "__main__":
    main()
