#!/usr/bin/env python3
"""The two checks that the kernel runs, on families that grow.

1. The saturated set (`refutedFast`, `DILL/SatFast.lean`), on the family
   "the chain with its last link missing" (`Corpus.chainBad`): the set
   the producer makes; the compiled check that is run and the compiled
   check of the definition (`refutedBy`), by `dillrun settime`; and the
   file that `dillrun prove` prints, elaborated: the kernel checks the
   set, in one run or in parts.  Beside it, to 76 sequents, the
   definition's check run by the kernel (`refutedBy … = true := by
   decide +kernel`): what the kernel did before the repair.  (Not
   beyond: see the comment in `sets`.)

2. The tree of moves (`step`, by `Move.ruleF`, `DILL/Proof.lean`), on the
   families `chain` and `fan`: the compiled check, by `dillrun cert`, and
   the fact stated with the tree, elaborated.

Every run of Lean has a cap on memory (`-M 4000`) and a deadline that
ends the whole process group, and they are made one at a time.  The
time of a file is that of the whole process less the time to load the
imports; the peak of memory is the process's (`/usr/bin/time -l`), the
imports included.

Run from `calculi/DILL/` after `lake build DILL dillrun`:
    python3 -I Corpus/measure_checks.py [sets] [trees]
"""
import subprocess, os, signal, sys, time, platform, datetime

EXE = ".lake/build/bin/dillrun"
OUT = "Corpus/out/checks"
MEM = 4000
DEADLINE = 300.0
COMPILED_DEADLINE = 120.0


def run(cmd, deadline):
    """Exit code (None at the deadline), seconds, output, error stream."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    t = time.monotonic()
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, time.monotonic() - t, out, err
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, err = p.communicate()
        return None, time.monotonic() - t, out, err


def lean(path):
    """Elaborate a file: exit code, seconds, peak of memory in MB, what it said."""
    code, dt, out, err = run(["/usr/bin/time", "-l", "lake", "env", "lean", "-M", str(MEM), path],
                             DEADLINE)
    rss = [l for l in err.splitlines() if "maximum resident" in l]
    mb = int(rss[0].split()[0]) / 1e6 if rss else 0
    said = [l for l in (out + err).splitlines() if "error" in l][:1]
    return code, dt, mb, said


def cell(code, dt, mb, said, base):
    if code is None:
        return f"not settled in {DEADLINE:.0f} s"
    if code != 0:
        why = ("stopped at the cap on memory" if mb > MEM * 0.95 or code in (134, -6)
               else (said[0][-70:] if said else f"exit code {code}"))
        return f"refused: {why} (after {dt:.0f} s, {mb:.0f} MB)"
    return f"{max(dt - base, 0):.2f} s, {mb:.0f} MB"


def fields(out):
    d = {}
    for tok in out.split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            d[k] = v
    return d


def ms(us):
    return f"{int(us) / 1000:.1f} ms"


def head(base):
    print(f"Machine: {platform.machine()}, {platform.platform()}; Lean v4.31.0.  "
          f"Date: {datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')}.  "
          f"Each run of Lean: `-M {MEM}`, a deadline of {DEADLINE:.0f} s on the process group, "
          f"one at a time.  Loading the imports: {base:.2f} s, taken off the times; the peaks "
          f"of memory include it (about 1300 MB).")
    print()


def sets():
    os.makedirs(OUT, exist_ok=True)
    bp = f"{OUT}/_base.lean"
    open(bp, "w").write("import DILL.Engine\n")
    base = min(lean(bp)[1] for _ in range(2))
    head(base)
    print("| n | formulas in the sequent | the set: sequents | the compiled check that is run "
          "(`refutedFast`) | the compiled check of the definition (`refutedBy`) | "
          "`dillrun prove`, the whole process | the printed file: parts | "
          "the printed file, elaborated: the kernel checks the set | "
          "the definition's check, run by the kernel |")
    print("|---|---|---|---|---|---|---|---|---|")
    kernel_on, def_on, defk_on = True, True, True
    for n in range(1, 12):
        c, dt, out, _ = run([EXE, "settime", str(n)] + (["def"] if def_on else []), COMPILED_DEADLINE)
        f = fields(out)
        if "set" not in f:
            print(f"| {n} | {n + 1} | the producer: not settled in {COMPILED_DEADLINE:.0f} s | | | | | | |")
            break
        fast = ms(f["check_us"]) if "check_us" in f else "not settled"
        if not def_on:
            dfn = "not run"
        elif "checkdef_us" in f:
            dfn = ms(f["checkdef_us"])
            if int(f["checkdef_us"]) > 20_000_000:
                def_on = False
        else:
            dfn = f"not settled in {COMPILED_DEADLINE:.0f} s"
            def_on = False
        zone = ["a0"] + [f"a{i} -o a{i + 1}" for i in range(n - 1)]
        text = ", ".join(zone) + f" => a{n}"
        c, dtp, printed, _ = run([EXE, "prove", "--deadline=120", text], COMPILED_DEADLINE + 10)
        whole = f"{dtp:.2f} s" if c == 1 else f"exit code {c} after {dtp:.1f} s"
        parts = printed.count("\ntheorem part_") or 1
        path = f"{OUT}/set_{n}.lean"
        open(path, "w").write(printed)
        if kernel_on and c == 1:
            r = lean(path)
            kern = cell(*r, base)
            if r[0] != 0:
                kernel_on = False
        else:
            kern = "not run"
        # the definition's check in the kernel: the same file, with `checked` stated of `refutedBy`
        # Only to 76 sequents.  At 200 the kernel refuses it at the cap, and
        # `decide` then computes the check again in the elaborator to say
        # why: one such run reached 7395 MB under `-M 4000` before it stopped.
        if defk_on and n <= 5 and c == 1 and "theorem checked" in printed:
            cut = printed[:printed.index("\n/- The check in")] if parts > 1 else \
                printed[:printed.index("\n/-- The kernel computes the check")]
            dpath = f"{OUT}/setdef_{n}.lean"
            open(dpath, "w").write(cut + "\ntheorem checkedDef : refutedBy saturated sequent = true := "
                                   "by decide +kernel\n\nend DILL.Answer\n")
            r = lean(dpath)
            dk = cell(*r, base)
            if r[0] != 0:
                defk_on = False
        else:
            dk = "not run"
        print(f"| {n} | {f['formulas']} | {f['set']} | {fast} | {dfn} | {whole} | {parts} | {kern} | {dk} |")
        sys.stdout.flush()
        if not kernel_on and not def_on:
            # the producer and the compiled check go on; the kernel's columns have stopped
            pass


def trees():
    os.makedirs(OUT, exist_ok=True)
    bp = f"{OUT}/_base_tree.lean"
    open(bp, "w").write("import DILL.Corpus.Basic\n")
    base = min(lean(bp)[1] for _ in range(2))
    head(base)
    print("| family | n | formulas in the sequent | the tree: moves | the search | "
          "the compiled check of the tree | the fact with the tree, elaborated: "
          "the kernel checks the tree |")
    print("|---|---|---|---|---|---|---|")
    for fam in ["chain", "fan"]:
        kernel_on = True
        for n in [8, 16, 32, 64, 96, 128, 192, 256]:
            c, dt, out, _ = run([EXE, "cert", "focus", fam, str(n), "0"], COMPILED_DEADLINE)
            lines = out.splitlines()
            size = next((l.split("size ")[1].split(",")[0] for l in lines if "size " in l), "?")
            su = next((l.split(": ")[1] for l in lines if l.startswith("search us")), None)
            cu = next((l.split(": ")[1] for l in lines if l.startswith("check us")), None)
            if cu is None:
                print(f"| {fam} | {n} | {n + 1} | {size} | not settled in {COMPILED_DEADLINE:.0f} s | | |")
                break
            path = f"Corpus/out/run/{fam}_{n}_focus_tree.lean"
            if kernel_on:
                r = lean(path)
                kern = cell(*r, base)
                if r[0] != 0:
                    kernel_on = False
            else:
                kern = "not run"
            print(f"| {fam} | {n} | {n + 1} | {size} | {ms(su)} | {ms(cu)} | {kern} |")
            sys.stdout.flush()


which = sys.argv[1:] or ["sets", "trees"]
if "sets" in which:
    print("### The saturated set\n")
    sets()
    print()
if "trees" in which:
    print("### The tree of moves\n")
    trees()
