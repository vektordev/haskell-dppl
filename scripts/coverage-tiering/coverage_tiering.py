#!/usr/bin/env python3
"""Coverage-informed test tiering: which default-suite tests add cost but no coverage.

Offline tool, not part of ``stack test`` (docs-repo task
``coverage-informed-test-tiering``; docs/testing.md, "Coverage-informed
tiering"). It answers: if a unit of the default suite were moved to ``Slow``,
would the rest of the default suite still execute every piece of code it does?

Pipeline (each step is a subcommand; ``all`` runs them in order):

  build     Build library, exe and both test suites with HPC instrumentation
            into a separate stack work dir (``.stack-work-coverage``), so the
            normal ``.stack-work`` is untouched.
  timings   Run the normal (uninstrumented) suite once with
            ``TASTY_HIDE_SUCCESSES=false NEST_FULL_TESTS=1`` and keep the log:
            the per-test times are the cost of each unit. ``--log FILE`` reuses
            an existing log of such a run instead. Run it on an idle machine.
  units     List the default tier of both binaries (``-l``) and partition it
            into units: one per corpus program across every whole-corpus sweep
            it appears in, one per non-corpus test group (two levels deep), one
            per Corpus-binary property.
  run       Run the instrumented binary once per unit (``-p`` selecting exactly
            the unit's tests, ``NEST_FULL_TESTS=1``) with its own HPCTIXFILE,
            and record the unit's tick set. Child processes are covered too:
            ``haskell-dppl-exe`` (TestCLI) writes its own tix, and ``python3`` /
            the torch python run under pytrace.py, which records the lines of
            pythonLib.py / pythonLibBatched.py executed. Julia is not covered.
            Resumable: units with a result are skipped unless ``--force``.
  analyze   Greedy weighted set cover over the units' tick sets (most new ticks
            per second of cost first, then a reverse-delete pass dropping cover
            units the rest already subsume). Units outside the cover are
            demotion candidates. Writes ``report.csv`` and ``report.md``.

Nothing is moved automatically: the report is for a human to decide from.

Usage (from anywhere; paths default to this checkout):

  scripts/coverage-tiering/coverage_tiering.py all -j 4
  scripts/coverage-tiering/coverage_tiering.py run -j 4 --only 'corpus:dice'
  scripts/coverage-tiering/coverage_tiering.py analyze

Outputs land in ``.stack-work-coverage/tiering/`` (``--out`` to change).
A full run on a 4-core machine takes roughly an hour, most of it in ``run``.
"""

import argparse
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
WORK_DIR = ".stack-work-coverage"
MAIN_SUITE = "haskell-dppl-test"
CORPUS_SUITE = "haskell-dppl-test-corpus"
EXE = "haskell-dppl-exe"
# A whole-corpus sweep is a test group with at least this many children named
# after corpus programs. Smaller per-program groups (BranchCountBackends' five
# hand-picked programs, say) are ordinary groups: a `.tst` slow header would
# not remove a program from them.
SWEEP_MIN_PROGRAMS = 10
# Units whose cost is below this are costed at it, so a free unit still has a
# finite coverage-per-second ratio.
MIN_COST = 0.005


def log(msg):
    print(msg, file=sys.stderr, flush=True)


# --------------------------------------------------------------------------
# build


def stack(args, repo, **kw):
    return subprocess.run(["stack"] + args, cwd=repo, **kw)


def cmd_build(a):
    r = stack(["--work-dir", WORK_DIR, "build", "--coverage", "--test", "--no-run-tests"], a.repo)
    if r.returncode != 0:
        sys.exit("coverage build failed")


def dist_dir(repo, work_dir=None):
    args = (["--work-dir", work_dir] if work_dir else []) + ["path", "--dist-dir"]
    out = stack(args, repo, capture_output=True, text=True, check=True).stdout.strip()
    return os.path.join(repo, out)


def binary(repo, name, work_dir=WORK_DIR):
    p = os.path.join(dist_dir(repo, work_dir), "build", name, name)
    if not os.path.exists(p):
        sys.exit("missing %s (run the build step)" % p)
    return p


# --------------------------------------------------------------------------
# timings


LEAF = re.compile(r"^( *)(.*?):\s+(OK|FAIL)\b(?: \((\d+\.\d+)s\))?")
SPLIT_LEAF = re.compile(r"^( *)(.*?):\s{2,}\S")
STATUS = re.compile(r"^(OK|FAIL)\b(?: \((\d+\.\d+)s\))?")


def parse_timings(path, known):
    """Per-test seconds from a TASTY_HIDE_SUCCESSES=false log.

    The log is an indented tree (two spaces per level). Group lines carry no
    status; leaf lines end in OK/FAIL and an optional time (tasty omits times
    below 0.01 s, taken as 0). Lines that are neither (QuickCheck output,
    stderr from tests) are skipped: a candidate group line is only pushed if
    some listed test starts with the name it would give.
    """
    prefixes = set()
    for t in known:
        parts = t.split(".")
        for i in range(1, len(parts)):
            prefixes.add(".".join(parts[:i]))
    times = {}
    stack_ = []  # (indent, name)
    pending = None  # a leaf whose status a test's stderr pushed onto the next line
    for raw in open(path, errors="replace"):
        line = raw.rstrip("\n")
        if not line.strip():
            continue
        if pending:
            m = STATUS.match(line)
            if m:
                times[pending] = times.get(pending, 0.0) + float(m.group(2) or 0.0)
                pending = None
                continue
        pending = None
        indent = len(line) - len(line.lstrip(" "))
        m = SPLIT_LEAF.match(line)
        if m and not LEAF.match(line):
            full = ".".join([n for i, n in stack_ if i < indent] + [m.group(2)])
            if full in known:
                pending = full
                continue
        m = LEAF.match(line)
        if m:
            while stack_ and stack_[-1][0] >= indent:
                stack_.pop()
            full = ".".join([n for _, n in stack_] + [m.group(2)])
            if full in known:
                times[full] = times.get(full, 0.0) + float(m.group(4) or 0.0)
            continue
        if indent % 2:
            continue
        name = line.strip()
        cand = [n for i, n in stack_ if i < indent]
        full = ".".join(cand + [name])
        if full in prefixes:
            while stack_ and stack_[-1][0] >= indent:
                stack_.pop()
            stack_.append((indent, name))
    return times


def cmd_timings(a):
    os.makedirs(a.out, exist_ok=True)
    dest = os.path.join(a.out, "timings.log")
    if a.log:
        shutil.copyfile(a.log, dest)
        return
    stack(["build", "--test", "--no-run-tests"], a.repo, check=True)
    env = dict(os.environ, TASTY_HIDE_SUCCESSES="false", NEST_FULL_TESTS="1")
    env.pop("NEST_SLOW_TESTS", None)
    env.pop("NEST_ASPIRATIONAL_TESTS", None)
    t0 = time.time()
    with open(dest, "w") as f:
        r = stack(["test"], a.repo, env=env, stdout=f, stderr=subprocess.STDOUT)
    log("timing run: exit %d, %.0f s wall" % (r.returncode, time.time() - t0))
    if r.returncode != 0:
        sys.exit("the timing run was not green; costs from a red run are not trusted")


# --------------------------------------------------------------------------
# units


def list_tests(repo, suite, out_dir):
    env = dict(os.environ)
    for v in ("NEST_SLOW_TESTS", "NEST_ASPIRATIONAL_TESTS", "NEST_SUPERSLOW_TESTS"):
        env.pop(v, None)
    # The instrumented binary writes a tix file even for -l; keep it out of the checkout.
    tix = os.path.join(out_dir, "list-%s.tix" % suite)
    env["HPCTIXFILE"] = tix
    out = subprocess.run([binary(repo, suite), "-l"], cwd=repo, env=env,
                         capture_output=True, text=True, check=True).stdout
    if os.path.exists(tix):
        os.remove(tix)
    return [l for l in out.splitlines() if l.strip()]


def corpus_names(repo):
    names = set()
    for root, _, files in os.walk(os.path.join(repo, "test", "cases")):
        for f in files:
            if f.endswith(".ppl"):
                names.add(f[:-4])
    return names


def partition(main_tests, corpus_tests, names):
    """Map each default-tier test to its unit."""
    # Which group prefixes are whole-corpus sweeps.
    per_prefix = defaultdict(set)
    hits = {}
    for t in main_tests:
        c = t.split(".")
        for i in range(2, len(c)):
            if c[i] in names:
                prefix = ".".join(c[:i])
                per_prefix[prefix].add(c[i])
                hits[t] = (prefix, c[i])
                break
    sweeps = {p for p, s in per_prefix.items() if len(s) >= SWEEP_MIN_PROGRAMS}
    units = defaultdict(list)
    for t in main_tests:
        h = hits.get(t)
        if h and h[0] in sweeps:
            units["corpus:" + h[1]].append(t)
        else:
            c = t.split(".")
            units["group:" + ".".join(c[:3] if len(c) >= 4 else c[:2])].append(t)
    for t in corpus_tests:
        units["corpusbin:" + t].append(t)
    return units, sorted(sweeps)


def cmd_units(a):
    names = corpus_names(a.repo)
    main_tests = list_tests(a.repo, MAIN_SUITE, a.out)
    corpus_tests = list_tests(a.repo, CORPUS_SUITE, a.out)
    units, sweeps = partition(main_tests, corpus_tests, names)
    tl = os.path.join(a.out, "timings.log")
    times = parse_timings(tl, set(main_tests) | set(corpus_tests)) if os.path.exists(tl) else {}
    missing = [t for t in main_tests + corpus_tests if t not in times]
    if times and missing:
        log("%d listed tests have no time in timings.log (costed 0), e.g. %s"
            % (len(missing), missing[:3]))
    doc = {
        "sweeps": sweeps,
        "units": {
            u: {
                "binary": CORPUS_SUITE if u.startswith("corpusbin:") else MAIN_SUITE,
                "tests": ts,
                "cost": round(sum(times.get(t, 0.0) for t in ts), 3),
            }
            for u, ts in sorted(units.items())
        },
    }
    json.dump(doc, open(os.path.join(a.out, "units.json"), "w"), indent=1)
    kinds = Counter(u.split(":")[0] for u in units)
    log("%d units (%s) over %d + %d tests; %d sweeps recognised"
        % (len(units), ", ".join("%d %s" % (n, k) for k, n in sorted(kinds.items())),
           len(main_tests), len(corpus_tests), len(sweeps)))


# --------------------------------------------------------------------------
# run


TIXMOD = re.compile(r'TixModule "([^"]*)" (\d+) (\d+) \[([^\]]*)\]')


def read_tix(path, into):
    """OR one tix file's hit ticks into ``into``: {module#hash: bitmask int}."""
    text = open(path).read()
    for name, h, n, counts in TIXMOD.findall(text):
        key = "%s#%s/%s" % (name, h, n)
        mask = 0
        for i, c in enumerate(counts.split(",")):
            if c and c != "0":
                mask |= 1 << i
        into[key] = into.get(key, 0) | mask


def read_py(path, into):
    for line in open(path):
        f, ln = line.strip().rsplit(":", 1)
        key = "py:" + f
        into[key] = into.get(key, 0) | (1 << int(ln))


def awk_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def write_shims(shim_dir, real_exe):
    os.makedirs(shim_dir, exist_ok=True)
    real_py = shutil.which("python3")
    torch_py = os.environ.get("NEST_TORCH_PYTHON") or os.path.expanduser(
        "~/.cache/nest/torchvenv/bin/python")
    shims = {
        # The exe is instrumented too: give each invocation its own tix file
        # (it would otherwise read the parent's, whose Main differs).
        EXE: '#!/bin/sh\nHPCTIXFILE="$NEST_COV_DIR/exe-$$.tix" exec %s "$@"\n' % real_exe,
        "python3": '#!/bin/sh\nexec %s %s/pytrace.py "$@"\n' % (real_py, HERE),
    }
    if os.path.exists(torch_py):
        shims["torch-python"] = '#!/bin/sh\nexec %s %s/pytrace.py "$@"\n' % (torch_py, HERE)
    for n, body in shims.items():
        p = os.path.join(shim_dir, n)
        open(p, "w").write(body)
        os.chmod(p, 0o755)
    return os.path.join(shim_dir, "torch-python") if "torch-python" in shims else None


def worker_dir(repo, base, k):
    """A cwd per worker: symlinks to the checkout plus a private .stack-work,
    so concurrent runs don't share the impact-analysis manifest."""
    d = os.path.join(base, "w%d" % k)
    if not os.path.isdir(d):
        os.makedirs(os.path.join(d, ".stack-work"))
        for e in os.listdir(repo):
            if e.startswith(".stack-work") or e == ".git":
                continue
            os.symlink(os.path.join(repo, e), os.path.join(d, e))
    return d


def run_unit(a, name, unit, bins, slot, shim_dir, torch_shim):
    res_dir = os.path.join(a.out, "ticks")
    safe = re.sub(r"[^A-Za-z0-9_.-]", "_", name)
    cov = os.path.join(a.out, "tmp", safe)
    shutil.rmtree(cov, ignore_errors=True)
    os.makedirs(cov)
    pattern = " || ".join("$0 == " + awk_str(t) for t in unit["tests"])
    env = dict(os.environ)
    for v in ("NEST_SLOW_TESTS", "NEST_ASPIRATIONAL_TESTS", "NEST_SUPERSLOW_TESTS",
              "NEST_SKIP_TORCH"):
        env.pop(v, None)
    env.update(HPCTIXFILE=os.path.join(cov, "main.tix"), NEST_COV_DIR=cov,
               NEST_FULL_TESTS="1", TASTY_HIDE_SUCCESSES="true",
               PATH=shim_dir + os.pathsep + env["PATH"])
    if torch_shim:
        env["NEST_TORCH_PYTHON"] = torch_shim
    cwd = worker_dir(a.repo, os.path.join(a.out, "workers"), slot)
    t0 = time.time()
    try:
        r = subprocess.run([bins[unit["binary"]], "-p", pattern, "+RTS", "-N%d" % a.cores, "-RTS"],
                           cwd=cwd, env=env, capture_output=True, text=True, timeout=a.timeout)
        code, out = r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired as e:
        code, out = "timeout", str(e.stdout or "")
    wall = time.time() - t0
    ran = re.search(r"All (\d+) tests passed|(\d+) out of (\d+) tests failed", out)
    ticks = {}
    for f in os.listdir(cov):
        p = os.path.join(cov, f)
        if f.endswith(".tix"):
            read_tix(p, ticks)
        elif f.startswith("py-"):
            read_py(p, ticks)
    result = {
        "unit": name, "exit": code, "wall": round(wall, 2),
        "summary": ran.group(0) if ran else None,
        "tail": out[-2000:] if code != 0 else "",
        "ticks": {k: format(v, "x") for k, v in ticks.items() if v},
    }
    json.dump(result, open(os.path.join(res_dir, safe + ".json"), "w"))
    shutil.rmtree(cov, ignore_errors=True)
    return name, code, wall, result["summary"]


def cmd_run(a):
    units = json.load(open(os.path.join(a.out, "units.json")))["units"]
    os.makedirs(os.path.join(a.out, "ticks"), exist_ok=True)
    bins = {s: binary(a.repo, s) for s in (MAIN_SUITE, CORPUS_SUITE)}
    shim_dir = os.path.join(a.out, "shims")
    torch_shim = write_shims(shim_dir, binary(a.repo, EXE))
    todo = []
    for n, u in units.items():
        if a.only and not re.search(a.only, n):
            continue
        safe = re.sub(r"[^A-Za-z0-9_.-]", "_", n)
        if not a.force and os.path.exists(os.path.join(a.out, "ticks", safe + ".json")):
            continue
        todo.append(n)
    # Longest first, so the tail of the run isn't one slow unit.
    todo.sort(key=lambda n: -units[n]["cost"])
    log("%d units to run, %d workers" % (len(todo), a.jobs))
    slots = list(range(a.jobs))
    done = 0
    t0 = time.time()
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        futs = {}

        def submit(n):
            slot = slots.pop()
            f = ex.submit(run_unit, a, n, units[n], bins, slot, shim_dir, torch_shim)
            futs[f] = slot

        pending = list(todo)
        while pending and slots:
            submit(pending.pop(0))
        while futs:
            for f in cf.as_completed(list(futs)):
                slots.append(futs.pop(f))
                n, code, wall, summ = f.result()
                done += 1
                flag = "" if code == 0 else "  [exit %s]" % code
                log("[%d/%d %4.0fs] %s: %.1fs %s%s" % (done, len(todo), time.time() - t0,
                                                     n, wall, summ or "", flag))
                if pending:
                    submit(pending.pop(0))
                break


# --------------------------------------------------------------------------
# analyze


def load_results(out, units):
    res = {}
    for n in units:
        safe = re.sub(r"[^A-Za-z0-9_.-]", "_", n)
        p = os.path.join(out, "ticks", safe + ".json")
        if os.path.exists(p):
            res[n] = json.load(open(p))
    return res


def to_bitsets(results):
    """Give every (module, tick) one bit position; each unit becomes one int."""
    width = {}
    for r in results.values():
        for k, v in r["ticks"].items():
            width[k] = max(width.get(k, 0), int(v, 16).bit_length())
    offsets, pos = {}, 0
    for k in sorted(width):
        offsets[k] = pos
        pos += width[k]
    sets = {}
    for n, r in results.items():
        s = 0
        for k, v in r["ticks"].items():
            s |= int(v, 16) << offsets[k]
        sets[n] = s
    return sets, offsets, width


def greedy_cover(sets, cost, universe, fixed):
    covered = 0
    chosen = []
    for n in fixed:
        covered |= sets[n]
        chosen.append(n)
    rest = [n for n in sets if n not in fixed]
    while covered != universe:
        best, best_ratio = None, -1.0
        for n in rest:
            gain = (sets[n] & ~covered).bit_count()
            if gain and gain / cost[n] > best_ratio:
                best, best_ratio = n, gain / cost[n]
        chosen.append(best)
        covered |= sets[best]
        rest.remove(best)
    # Reverse delete: drop the most expensive cover units the others subsume.
    for n in sorted([c for c in chosen if c not in fixed], key=lambda c: -cost[c]):
        others = 0
        for m in chosen:
            if m != n:
                others |= sets[m]
        if others == universe:
            chosen.remove(n)
    return chosen


def subsumers(target, cover, sets, limit=4):
    """A few cover units that together cover ``target``'s ticks, greedily."""
    need, picks = target, []
    while need and len(picks) < limit:
        best = max(cover, key=lambda m: (sets[m] & need).bit_count())
        got = (sets[best] & need).bit_count()
        if not got:
            break
        picks.append((best, got))
        need &= ~sets[best]
    return picks


def cmd_analyze(a):
    doc = json.load(open(os.path.join(a.out, "units.json")))
    units = doc["units"]
    results = load_results(a.out, units)
    missing = sorted(set(units) - set(results))
    failed = sorted(n for n, r in results.items() if r["exit"] != 0)
    usable = {n: r for n, r in results.items() if r["ticks"]}
    sets, offsets, width = to_bitsets(usable)
    cost = {n: max(units[n]["cost"], MIN_COST) for n in sets}
    universe = 0
    for s in sets.values():
        universe |= s
    # Julia's runtime is invisible here, so a unit holding Julia checks is
    # never a candidate; it seeds the cover instead.
    fixed = sorted(n for n in sets if any(".Julia" in t for t in units[n]["tests"]))
    cover = greedy_cover(sets, cost, universe, fixed)
    cover_set = set(cover)
    cand = sorted((n for n in sets if n not in cover_set), key=lambda n: -cost[n])

    # Ticks only one unit has: what demoting it would lose outright.
    once = multi = 0
    for s_ in sets.values():
        multi |= once & s_
        once = (once | s_) & ~multi
    unique = {n: (s_ & once).bit_count() for n, s_ in sets.items()}

    total_cost = sum(units[n]["cost"] for n in units)
    cand_cost = sum(units[n]["cost"] for n in cand)
    py_cov = sum((universe >> offsets[k] & ((1 << width[k]) - 1)).bit_count()
                 for k in width if k.startswith("py:"))

    with open(os.path.join(a.out, "report.csv"), "w") as f:
        f.write("unit,kind,tests,cost_s,in_cover,ticks,unique_ticks,run_exit,subsumed_by\n")
        for n in sorted(units, key=lambda n: -units[n]["cost"]):
            u = units[n]
            s = sets.get(n, 0)
            sub = ""
            if n in sets and n not in cover_set:
                sub = "; ".join("%s(%d)" % (m, g) for m, g in subsumers(s, cover, sets))
            f.write('"%s",%s,%d,%.3f,%s,%d,%d,%s,"%s"\n' % (
                n.replace('"', '""'), n.split(":")[0], len(u["tests"]), u["cost"],
                "fixed" if n in fixed else ("yes" if n in cover_set else "no"),
                s.bit_count(), unique.get(n, 0),
                results[n]["exit"] if n in results else "missing", sub.replace('"', '""')))

    by_kind = defaultdict(lambda: [0, 0.0])
    for n in cand:
        by_kind[n.split(":")[0]][0] += 1
        by_kind[n.split(":")[0]][1] += units[n]["cost"]
    lines = []
    w = lines.append
    w("# Coverage-informed tiering report")
    w("")
    w("Generated by `scripts/coverage-tiering/coverage_tiering.py analyze` at %s."
      % time.strftime("%Y-%m-%d %H:%M"))
    w("")
    w("## Summary")
    w("")
    w("- Units: %d (%s); %d ran, %d missing, %d exited non-zero."
      % (len(units), ", ".join("%d %s" % (c, k) for k, c in
                               sorted(Counter(n.split(':')[0] for n in units).items())),
         len(results), len(missing), len(failed)))
    w("- Tick universe (everything the default suite executes): %d HPC ticks in %d modules, "
      "plus %d distinct lines of pythonLib.py / pythonLibBatched.py."
      % (universe.bit_count() - py_cov, sum(1 for k in width if not k.startswith("py:")),
         py_cov))
    common = universe
    for s_ in sets.values():
        common &= s_
    w("- %d of those ticks are executed by every unit (process start-up: parsing the corpus, "
      "building the tree), so a unit's own contribution is its count minus that."
      % common.bit_count())
    w("- Summed test time of all units: %.1f s." % total_cost)
    w("- Cover: %d units (%d fixed: they hold Julia checks), %.1f s summed."
      % (len(cover), len(fixed), sum(units[n]["cost"] for n in cover)))
    w("- **Demotion candidates: %d units, %.1f s summed (%.0f%% of the total).** "
      "Every tick they execute is also executed by the cover."
      % (len(cand), cand_cost, 100 * cand_cost / total_cost if total_cost else 0))
    w("  This holds jointly, not just one at a time: the cover stays in the default tier, so "
      "demoting any subset of the candidates loses no tick.")
    for k, (c, s) in sorted(by_kind.items()):
        w("  - %s: %d units, %.1f s" % (k, c, s))
    w("")
    w("Summed test time is not wall time: the suite runs tests in parallel, so demoting "
      "X s of summed time saves roughly X / (cores in use) of wall time, less where the "
      "critical path is one long test.")
    w("")
    w("## Caveats")
    w("")
    w("- **Tick coverage is not value coverage.** Two corpus programs can take the same "
      "code paths and pin different numbers. A demoted unit still runs in `Slow` before "
      "every merge, so the risk is a later catch, not a lost one.")
    w("- **Julia's runtime is invisible.** `juliaLib.jl` is not covered, so units holding "
      "Julia checks are fixed in the cover. Demoting a corpus program with a `.tst` `slow` "
      "header also takes it out of the Julia shards, which this analysis cannot weigh.")
    w("- **Python's runtime is line coverage** of `pythonLib.py` and `pythonLibBatched.py` "
      "(pytrace.py), coarser than HPC's expression ticks.")
    w("- **The harness counts.** Ticks in the test modules (End2EndTesting, "
      "TestCaseParser, ...) are part of the universe, deliberately.")
    w("- **Randomness.** The Corpus-binary properties and the fuzz groups draw programs at "
      "random, so their tick sets vary from run to run; a unit covered only by such a unit "
      "is covered by chance.")
    w("- **Greedy, not optimal.** Weighted set cover is NP-hard; the cover is greedy "
      "(new ticks per second) followed by a reverse-delete pass. A different cover can "
      "make a different set of candidates.")
    w("- **Staleness.** Coverage moves with the code. Re-run when the suite has grown "
      "materially, not on a schedule.")
    w("")
    w("## Candidates, most expensive first")
    w("")
    w("`subsumed by` lists up to four cover units that together cover the candidate's "
      "ticks, with the number of the candidate's ticks each contributes.")
    w("")
    w("| unit | tests | cost s | ticks | subsumed by |")
    w("|---|---:|---:|---:|---|")
    for n in cand[: a.top]:
        sub = ", ".join("`%s` (%d)" % (m, g) for m, g in subsumers(sets[n], cover, sets))
        w("| `%s` | %d | %.2f | %d | %s |" % (n, len(units[n]["tests"]), units[n]["cost"],
                                            sets[n].bit_count(), sub))
    if len(cand) > a.top:
        w("")
        w("%d more in `report.csv`." % (len(cand) - a.top))
    w("")
    w("## The most expensive cover units")
    w("")
    w("These stay. `unique` is the number of ticks no other unit executes.")
    w("")
    w("| unit | cost s | ticks | unique |")
    w("|---|---:|---:|---:|")
    for n in sorted(cover, key=lambda n: -cost[n])[:25]:
        w("| `%s` | %.2f | %d | %d |" % (n, units[n]["cost"], sets[n].bit_count(), unique.get(n, 0)))
    if failed or missing:
        w("")
        w("## Units that failed or did not run")
        w("")
        w("A non-zero exit still yields the ticks executed up to the end of the run "
          "(a timeout yields none). These are listed so a reader can judge them.")
        w("")
        for n in failed:
            r = results[n]
            w("- `%s`: exit %s, %s" % (n, r["exit"], r["summary"] or "no summary"))
        for n in missing:
            w("- `%s`: no result" % n)
    open(os.path.join(a.out, "report.md"), "w").write("\n".join(lines) + "\n")
    log("cover %d units, %d candidates (%.1f s of %.1f s); report in %s"
        % (len(cover), len(cand), cand_cost, total_cost, a.out))


# --------------------------------------------------------------------------


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--repo", default=REPO, help="the checkout to analyse (default: this one)")
    p.add_argument("--out", default=None, help="output dir (default: <repo>/%s/tiering)" % WORK_DIR)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("build")
    t = sub.add_parser("timings")
    t.add_argument("--log", help="reuse an existing TASTY_HIDE_SUCCESSES=false NEST_FULL_TESTS=1 log")
    sub.add_parser("units")
    for name in ("run", "all"):
        r = sub.add_parser(name)
        r.add_argument("-j", "--jobs", type=int, default=4, help="units run concurrently")
        r.add_argument("--cores", type=int, default=1, help="+RTS -N per unit process")
        r.add_argument("--timeout", type=int, default=1800, help="seconds per unit")
        r.add_argument("--only", help="regex on unit names")
        r.add_argument("--force", action="store_true", help="rerun units that have a result")
        r.add_argument("--top", type=int, default=60, help="candidates listed in report.md")
        if name == "all":
            r.add_argument("--log", help="as for timings")
    an = sub.add_parser("analyze")
    an.add_argument("--top", type=int, default=60, help="candidates listed in report.md")
    a = p.parse_args()
    a.repo = os.path.abspath(a.repo)
    a.out = os.path.abspath(a.out or os.path.join(a.repo, WORK_DIR, "tiering"))
    os.makedirs(a.out, exist_ok=True)
    if a.cmd == "all":
        cmd_build(a)
        cmd_timings(a)
        cmd_units(a)
        cmd_run(a)
        cmd_analyze(a)
    else:
        {"build": cmd_build, "timings": cmd_timings, "units": cmd_units,
         "run": cmd_run, "analyze": cmd_analyze}[a.cmd](a)


if __name__ == "__main__":
    main()
