#!/usr/bin/env python3
"""Measurements of the Run stage, for the families of the corpus.

For each member of a family, in growing size:
  * the two compiled producers (`mallrun cert lazy|search`): the verdict,
    the size and nesting of the tree of moves, the time;
  * the fact stated with the lazy search's tree (`lake env lean` on the
    file the producer wrote): parsing and elaborating the tree as a term,
    and the kernel's check of it, less the time to load the imports;
  * the kernel running the proved search itself (`by decide +kernel` on
    `Derivable`, or on its negation).
Every run is under a deadline; a run cut off is a flag, and the column
stops there (rules R5, R7 of lean-certify).  Run from `calculi/MALL/`
after `lake build mallrun`:  python3 -I Corpus/measure.py > <report>
"""
import subprocess, time, os, platform, datetime

EXE = ".lake/build/bin/mallrun"
PRODUCER_DEADLINE = 20.0
KERNEL_DEADLINE = 30.0
FAMILIES = {
    "chain": [2, 4, 6, 8, 10, 12, 16, 24, 32, 48, 64],
    "fan": [2, 4, 6, 8, 10, 12, 16, 24, 32, 48, 64],
    "slack": [2, 4, 8, 12, 16, 24, 32, 64],
    "withTree": [2, 4, 6, 8, 10, 12],
    "chainBad": [2, 4, 6, 8, 10, 12, 16],
    "fanBad": [2, 4, 6, 8, 10, 12, 16],
}
DERIVABLE = {"chain": True, "fan": True, "slack": True, "withTree": True,
             "chainBad": False, "fanBad": False}


def timed(cmd, deadline):
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=deadline)
        return time.monotonic() - t0, r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, None, ""


def lean(path, deadline):
    return timed(["lake", "env", "lean", path], deadline)


def check(path, base):
    """One fact file: its time less the imports, or why it is a flag."""
    tc, rcc, outc = lean(path, KERNEL_DEADLINE + base)
    if tc is None:
        return f"flag (> {KERNEL_DEADLINE:.0f} s)", False
    if rcc != 0:
        why = ("maximum recursion depth" if "maximum recursion" in outc
               else "deterministic timeout" if "timeout" in outc
               else outc.strip().splitlines()[0][-80:])
        return f"flag: not elaborated ({why})", False
    return f"{max(tc - base, 0):.2f} s", True


def producer(prod, fam, n):
    t, rc, out = timed([EXE, "cert", prod, fam, str(n)], PRODUCER_DEADLINE)
    if t is None:
        return None
    lines = out.strip().splitlines()
    verdict = lines[0].split(": ")[1].split(",")[0]
    size = lines[0].split("size ")[1].split(",")[0]
    depth = lines[0].split("depth ")[1]
    ms = lines[1].split(": ")[1]
    return verdict, size, depth, ms


os.makedirs("Corpus/out", exist_ok=True)
base_path = "Corpus/out/_base.lean"
open(base_path, "w").write("import MALL.Corpus.Basic\n")
base = min(lean(base_path, 60)[0] for _ in range(3))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.date.today()}.  Loading the imports: {base:.2f} s, "
      "taken off the times of the last two columns.")
print(f"Deadlines: each producer {PRODUCER_DEADLINE:.0f} s, each check "
      f"{KERNEL_DEADLINE:.0f} s.  `flag`: cut off at the deadline, or not "
      "elaborated; the column stops there.\n")
print("| family | n | formulas in the sequent | verdict | the lazy search: moves, nesting, time "
      "| the proved search: time | the fact with the lazy search's tree: elaborated, and checked "
      "by the kernel | the kernel running the proved search (`decide +kernel`) |")
print("|---|---|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    lazy_on, search_on, cert_on, dec_on = True, True, True, True
    for n in ns:
        if not (lazy_on or search_on or dec_on):
            break
        cell_l, cell_s, cell_c, cell_d = "not run", "not run", "not run", "not run"
        verdict = "?"
        if lazy_on:
            r = producer("lazy", fam, n)
            if r is None:
                cell_l, lazy_on = f"flag (> {PRODUCER_DEADLINE:.0f} s)", False
            else:
                verdict = "derivable" if r[0] == "pass" else "none found"
                cell_l = (f"{r[1]} moves, nesting {r[2]}, {r[3]} ms" if r[0] == "pass"
                          else f"none, {r[3]} ms")
                if r[0] == "pass" and cert_on:
                    cell_c, cert_on = check(f"Corpus/out/{fam}_{n}_lazy.lean", base)
                elif r[0] != "pass":
                    cell_c = "no tree: not a derivation"
        if search_on:
            r = producer("search", fam, n)
            if r is None:
                cell_s, search_on = f"flag (> {PRODUCER_DEADLINE:.0f} s)", False
            else:
                cell_s = f"{r[3]} ms" + ("" if r[0] == "pass" else " (none)")
        if dec_on:
            path = f"Corpus/out/{fam}_{n}_decide.lean"
            stmt = (f"Derivable (Corpus.{fam} {n})" if DERIVABLE[fam]
                    else f"¬ Derivable (Corpus.{fam} {n})")
            open(path, "w").write(
                "import MALL.Corpus.Basic\nopen MALL MALL.Corpus\n\n"
                f"example : {stmt} := by decide +kernel\n")
            td, rcd, outd = lean(path, KERNEL_DEADLINE + base)
            if td is None:
                cell_d, dec_on = f"flag (> {KERNEL_DEADLINE:.0f} s)", False
            elif rcd != 0:
                cell_d, dec_on = "flag: " + outd.strip().splitlines()[0][-80:], False
            else:
                cell_d = f"{max(td - base, 0):.2f} s"
        nforms = {"chain": n + 2, "chainBad": n + 2, "fan": n + 2, "fanBad": n + 2,
                  "slack": n + 2, "withTree": 2}[fam]
        print(f"| {fam} | {n} | {nforms} | {verdict if verdict != '?' else ('derivable' if DERIVABLE[fam] else 'not derivable')} "
              f"| {cell_l} | {cell_s} | {cell_c} | {cell_d} |", flush=True)
