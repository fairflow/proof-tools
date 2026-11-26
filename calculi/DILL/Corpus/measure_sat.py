#!/usr/bin/env python3
"""Measurements of the saturated sets (the "no" side of the Run stage).

For each member of the family "the chain with its last link missing",
in growing size, and for each of the producer's two ways to choose a
premise:
  * the compiled producer (`Corpus/SatMain.lean`): the sequents the
    search settles, the size of the set, the times of the search, of the
    cut to the set, and of the compiled check `refutedBy`;
  * the fact stated with the set (`lake env lean` on the file the driver
    wrote): parsing and elaborating the set as a term, and the kernel's
    evaluation of `refutedBy`, less the time to load the imports.
Every run is under a deadline; a run cut off is a flag, and its column
stops there (rules R5, R7 of lean-certify).

The driver is compiled here, into `Corpus/out/`, from the C files that
`lake build DILL.Refute` leaves and the object files of the library
(the lakefile has no executable for it); where that fails it is run by
`lake env lean --run`, and the report says so.

Run from `calculi/DILL/` after `lake build DILL.Refute DILL.SatRun`:
    python3 -I Corpus/measure_sat.py > <report>
    python3 -I Corpus/measure_sat.py decide > <report>     (the comparison:
        the kernel running the proved search of `DILL/Decide.lean`)
"""
import subprocess, time, os, glob, platform, datetime, sys

OUT = "Corpus/out"
PRODUCER_DEADLINE = 60.0
KERNEL_DEADLINE = 120.0
SIZES = list(range(1, 15))       # the family is bounded: at most n = 14
CHOICES = ["first", "shortest"]
MODULES = ["Form", "Perm", "System", "Decide", "Saturated", "Proof", "Tactic", "Refute"]


def timed(cmd, deadline):
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=deadline)
        return time.monotonic() - t0, r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, None, ""


def build_driver():
    """The driver as a native executable, or None."""
    try:
        prefix = subprocess.run(["lake", "env", "lean", "--print-prefix"], capture_output=True,
                                text=True, timeout=60).stdout.strip()
        leanc = os.path.join(prefix, "bin", "leanc")
        obj = os.path.join(OUT, "obj")
        os.makedirs(obj, exist_ok=True)
        subprocess.run(["lake", "env", "lean", "-c", f"{obj}/SatMain.c", "Corpus/SatMain.lean"],
                       check=True, timeout=120)
        for m in MODULES:
            subprocess.run([leanc, "-c", "-O3", "-DNDEBUG", "-o", f"{obj}/{m}.o",
                            f".lake/build/ir/DILL/{m}.c"], check=True, timeout=300)
        subprocess.run([leanc, "-c", "-O3", "-DNDEBUG", "-o", f"{obj}/SatMain.o",
                        f"{obj}/SatMain.c"], check=True, timeout=300)
        lib = glob.glob("../../.lake/build/ir/**/*.c.o.export", recursive=True)
        exe = os.path.join(OUT, "satmain")
        subprocess.run([leanc, "-o", exe] + [f"{obj}/{m}.o" for m in MODULES + ["SatMain"]] + lib,
                       check=True, timeout=300)
        return [exe]
    except Exception as e:  # noqa: BLE001
        print(f"(the driver was not compiled: {e})", file=sys.stderr)
        return None


def fields(out):
    d = {}
    for tok in out.split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            d[k] = v
    return d


def decide_mode():
    """The comparison: the kernel running the proved search of the fragment
    without `!` (`Dec.decCF`, `DILL/Decide.lean`) on the same family."""
    base_path = f"{OUT}/_base_decide.lean"
    open(base_path, "w").write("import DILL.Decide\n")
    base = min(timed(["lake", "env", "lean", base_path], 120)[0] for _ in range(3))
    print(f"Machine: {platform.machine()}, {platform.platform()}.  "
          f"Date: {datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')}.  "
          f"Loading the imports: {base:.2f} s, taken off.  Deadline {KERNEL_DEADLINE:.0f} s.")
    print()
    print("| n | formulas in the sequent | the kernel running the proved search (`decide +kernel`) |")
    print("|---|---|---|")
    for n in SIZES:
        zone = ["Form.atom 0"] + [f"Form.atom {i} ⊸ Form.atom {i + 1}" for i in range(n - 1)]
        path = f"{OUT}/SatDecide_{n}.lean"
        open(path, "w").write(
            "import DILL.Decide\nopen DILL DILL.Dec\n"
            f"example : ¬ Nonempty (CF ([] ⨾ [{', '.join(zone)}] ⟹ Form.atom {n})) := by\n"
            "  decide +kernel\n")
        tc, rcc, outc = timed(["lake", "env", "lean", path], KERNEL_DEADLINE + base)
        if tc is None:
            print(f"| {n} | {n + 1} | flag (> {KERNEL_DEADLINE:.0f} s) |")
            break
        if rcc != 0:
            print(f"| {n} | {n + 1} | flag: not elaborated ({outc.strip().splitlines()[0][-80:]}) |")
            break
        print(f"| {n} | {n + 1} | {max(tc - base, 0):.2f} s |")
        sys.stdout.flush()


os.makedirs(OUT, exist_ok=True)
if sys.argv[1:] == ["decide"]:
    decide_mode()
    sys.exit(0)
driver = build_driver()
compiled = driver is not None
if not compiled:
    driver = ["lake", "env", "lean", "--run", "Corpus/SatMain.lean"]

base_path = f"{OUT}/_base.lean"
open(base_path, "w").write("import DILL.SatRun\n")
base = min(timed(["lake", "env", "lean", base_path], 120)[0] for _ in range(3))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %Z')}.  "
      f"The driver: {'compiled (leanc -O3)' if compiled else 'run by `lean --run` (the interpreter)'}.  "
      f"Loading the imports of a fact: {base:.2f} s, taken off the last column.")
print(f"Deadlines: the producer {PRODUCER_DEADLINE:.0f} s, the fact {KERNEL_DEADLINE:.0f} s.  "
      "`flag`: cut off at the deadline, or not elaborated; the column stops there.")
print()
print("| n | formulas in the sequent | choice | settled by the search (of them \"no\") | "
      "the set: sequents, longest linear zone | search | cut to the set | compiled check | "
      "the fact: elaborated, and checked by the kernel |")
print("|---|---|---|---|---|---|---|---|---|")

for ch in CHOICES:
    kernel_on = True
    for n in SIZES:
        fact = f"{OUT}/SatFact_{ch}_{n}.lean"
        if os.path.exists(fact):
            os.remove(fact)
        t, rc, out = timed(driver + [str(n), ch, fact], PRODUCER_DEADLINE)
        if t is None:
            print(f"| {n} | {n + 1} | {ch} | flag (> {PRODUCER_DEADLINE:.0f} s) | | | | | |")
            sys.stdout.flush()
            break
        f = fields(out)
        if f.get("verdict") != "refuted":
            print(f"| {n} | {n + 1} | {ch} | {f.get('verdict', 'error: ' + out.strip()[-60:])} | | | | | |")
            sys.stdout.flush()
            break
        if kernel_on:
            tc, rcc, outc = timed(["lake", "env", "lean", fact], KERNEL_DEADLINE + base)
            if tc is None:
                kernel = f"flag (> {KERNEL_DEADLINE:.0f} s)"
                kernel_on = False
            elif rcc != 0:
                why = ("maximum recursion depth" if "maximum recursion" in outc
                       else "deterministic timeout" if "timeout" in outc
                       else outc.strip().splitlines()[0][-80:])
                kernel = f"flag: not elaborated ({why})"
                kernel_on = False
            else:
                kernel = f"{max(tc - base, 0):.2f} s"
        else:
            kernel = "not run"
        print(f"| {n} | {f['formulas']} | {ch} | {f['settled']} ({f['no']}) | "
              f"{f['set']}, {f['longest']} | {f['search_ms']} ms | {f['closure_ms']} ms | "
              f"{f['check_ms']} ms | {kernel} |")
        sys.stdout.flush()
