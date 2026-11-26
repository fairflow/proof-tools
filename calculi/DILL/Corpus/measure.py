#!/usr/bin/env python3
"""Measurements of the Run stage, "yes" side, for the families of the corpus.

For each member of a family, in growing size:
  * the compiled search with the left rules chained (`dillrun cert focus`):
    the verdict, the size and nesting of the tree of moves, the copies
    along a branch, the calls of the search, its time; and the time of
    the compiled check of the tree;
  * the compiled search with the left rules as the figure has them
    (`dillrun run plain`): its calls and time;
  * the fact stated with the tree (`lake env lean` on the file the driver
    wrote): parsing and elaborating the tree as a term and the kernel's
    check of it, one figure, less the time to load the imports (the least
    of three runs where a run is under 5 s);
  * the same with the script of the same derivation;
  * where the unrestricted zone is empty and `!` does not occur, the
    kernel running the proved search of `DILL/Decide.lean` on the sequent
    (`by decide +kernel`), with no certificate.
Every run is under a deadline; a run cut off is a flag, and the column
stops there (rules R5, R7 of lean-certify).  Every size is listed below:
nothing is generated without a bound.

Run from `calculi/DILL/`:

    python3 -I Corpus/measure.py > <report>

The driver is `.lake/build/bin/dillrun` (after `lake build dillrun`), or
the path in the environment variable DILLRUN.
"""
import subprocess, time, os, platform, datetime

EXE = os.environ.get("DILLRUN", ".lake/build/bin/dillrun")
OUT = "Corpus/out/run"
PRODUCER_DEADLINE = 20.0
KERNEL_DEADLINE = 60.0
SIZES = [2, 4, 8, 16, 32, 64, 96, 128, 256, 512, 1024, 2048, 4096]
FAMILIES = {
    "chain": SIZES,
    "chainU": SIZES,
    "fan": SIZES,
    "chainBad": [2, 4, 6, 8, 10, 12, 14, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096],
    "chainUBad": [2, 3, 4, 5, 6, 7, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096],
}
# the families that the proved search of `DILL/Decide.lean` covers
DECIDED = {"chain", "fan", "chainBad"}
DERIVABLE = {"chain": True, "chainU": True, "fan": True, "chainBad": False, "chainUBad": False}
# the copies allowed along a branch, and the formulas of the sequent
BUDGET = {"chain": lambda n: 0, "chainU": lambda n: n, "fan": lambda n: 0,
          "chainBad": lambda n: 0, "chainUBad": lambda n: n}
NFORMS = {"chain": lambda n: n + 2, "chainU": lambda n: n + 2, "fan": lambda n: n + 1,
          "chainBad": lambda n: n + 1, "chainUBad": lambda n: n + 1}


def timed(cmd, deadline):
    """The time, the return code and the output; on a cut, what was printed."""
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=deadline)
        return time.monotonic() - t0, r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired as e:
        out = e.stdout or b""
        return None, None, out.decode() if isinstance(out, bytes) else out


def lean(path, deadline):
    return timed(["lake", "env", "lean", path], deadline)


def check(path, base):
    """One fact file: its time less the imports, or why it is a flag."""
    tc, rcc, outc = lean(path, KERNEL_DEADLINE + base)
    if tc is not None and rcc == 0 and tc < 5:
        # a short one: the least of three, against the noise of the machine
        tc = min([tc] + [t for t in (lean(path, KERNEL_DEADLINE + base)[0] for _ in range(2))
                         if t is not None])
    if tc is None:
        return f"flag (> {KERNEL_DEADLINE:.0f} s)", False
    if rcc != 0:
        why = ("maximum recursion depth" if "maximum recursion" in outc
               else "deterministic timeout" if "timeout" in outc
               else "stack overflow" if "tack overflow" in outc
               else (outc.strip().splitlines() or [f"exit {rcc}"])[0][-80:])
        return f"flag: not elaborated ({why})", False
    return f"{max(tc - base, 0):.2f} s", True


def us(x):
    x = int(x)
    return f"{x / 1000:.1f} ms" if x < 10_000_000 else f"{x / 1e6:.1f} s"


def producer(cmd, mode, fam, n):
    """What the driver printed, as a dictionary; `cut` where it was cut off."""
    t, rc, out = timed([EXE, cmd, mode, fam, str(n), str(BUDGET[fam](n))], PRODUCER_DEADLINE)
    d = {"cut": t is None, "crash": t is not None and rc != 0}
    for line in out.strip().splitlines():
        if line.startswith(f"{fam} {n}: "):
            parts = line.split(": ", 1)[1].split(", ")
            d["verdict"] = parts[0]
            for part in parts[1:]:
                k, v = part.rsplit(" ", 1)
                d[k] = v
        elif line.startswith("search us: "):
            d["search"] = line.split(": ")[1]
        elif line.startswith("check us: "):
            d["check"] = line.split(": ")[1]
        elif line.startswith("check: "):
            d["ok"] = line.split(": ")[1]
    return d


os.makedirs(OUT, exist_ok=True)
base_path = f"{OUT}/_base.lean"
open(base_path, "w").write("import DILL.Corpus.Basic\n")
base = min(lean(base_path, 120)[0] for _ in range(5))
open(base_path, "w").write("import DILL.Decide\n")
base_dec = min(lean(base_path, 120)[0] for _ in range(5))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.datetime.now().astimezone():%Y-%m-%d %H:%M %Z}.  "
      f"Loading the imports: {base:.2f} s ({base_dec:.2f} s for the last column), "
      "taken off the times of the last three columns.")
print(f"Deadlines: each run of the driver {PRODUCER_DEADLINE:.0f} s (search and compiled "
      f"check together), each fact {KERNEL_DEADLINE:.0f} s.  `flag`: cut off at the deadline, "
      "or not elaborated; the column stops there.\n")
print("| family | n | formulas in the sequent | budget (copies along a branch) | status "
      "| the search, left rules chained: its answer, calls, time "
      "| the compiled check of its tree "
      "| the search, left rules as in the figure: its answer, calls, time "
      "| the fact with the tree: elaborated, and checked by the kernel "
      "| the fact with the script "
      "| the kernel running the proved search (`decide +kernel`) |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    focus_on, plain_on, tree_on, script_on = True, True, True, True
    dec_on = fam in DECIDED
    for n in ns:
        if not (focus_on or plain_on):
            break
        cell_f = cell_k = cell_p = cell_t = cell_s = "not run"
        cell_d = "not run" if fam in DECIDED else "not applicable"
        if focus_on:
            d = producer("cert", "focus", fam, n)
            if "verdict" not in d:
                cell_f = (f"flag (> {PRODUCER_DEADLINE:.0f} s)" if d["cut"]
                          else "flag: the driver stopped (stack)")
                focus_on = False
            else:
                if d["verdict"] == "pass":
                    cell_f = (f"a tree of {d['size']} moves, nesting {d['depth']}, "
                              f"{d['copies']} copies; {d['calls']} calls, {us(d['search'])}")
                else:
                    cell_f = (f"nothing ({d['calls']} calls, {d['refused']} copies refused), "
                              f"{us(d['search'])}")
                    cell_k = cell_t = cell_s = "no tree"
                if d["verdict"] == "pass":
                    if "check" in d:
                        cell_k = us(d["check"]) + ("" if d.get("ok") == "true" else " REFUSED")
                    else:
                        cell_k = (f"flag (> {PRODUCER_DEADLINE:.0f} s with the search)"
                                  if d["cut"] else "flag: the driver stopped (stack)")
                        focus_on = False
                    if "check" in d and d.get("ok") == "true":
                        if tree_on:
                            cell_t, tree_on = check(f"{OUT}/{fam}_{n}_focus_tree.lean", base)
                        if script_on:
                            cell_s, script_on = check(f"{OUT}/{fam}_{n}_focus_script.lean", base)
            if dec_on and os.path.exists(f"{OUT}/{fam}_{n}_decide.lean"):
                cell_d, dec_on = check(f"{OUT}/{fam}_{n}_decide.lean", base_dec)
        if plain_on:
            d = producer("run", "plain", fam, n)
            if "verdict" not in d:
                cell_p = (f"flag (> {PRODUCER_DEADLINE:.0f} s)" if d["cut"]
                          else "flag: the driver stopped (stack)")
                plain_on = False
            elif d["verdict"] == "pass":
                cell_p = f"a tree of {d['size']} moves; {d['calls']} calls, {us(d['search'])}"
                if "check" not in d:
                    plain_on = False
            else:
                cell_p = (f"nothing ({d['calls']} calls, {d['refused']} copies refused), "
                          f"{us(d['search'])}")
        print(f"| {fam} | {n} | {NFORMS[fam](n)} | {BUDGET[fam](n)} "
              f"| {'derivable' if DERIVABLE[fam] else 'not derivable'} "
              f"| {cell_f} | {cell_k} | {cell_p} | {cell_t} | {cell_s} | {cell_d} |", flush=True)
