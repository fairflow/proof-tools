#!/usr/bin/env python3
"""Measurements of the Run stage, for the four families of the corpus.

For each member of a family, in growing size:
  * the compiled producer (`glsrun cert`): its verdict, the size of its
    certificate, its time;
  * the fact stated with that certificate (`lake env lean` on the file the
    producer wrote): parsing and elaborating the certificate as a term,
    and the kernel's check of it, less the time to load the imports;
  * for a derivation, the same fact with its script in place of its tree;
  * for comparison, the kernel running the search itself
    (`by decide +kernel` on `Valid`).
Every run is under a deadline; a run cut off is a flag, and the column
stops there (rules R5, R7 of lean-certify).  Run from `calculi/GLS/`
after `lake build glsrun`:  python3 -I Corpus/measure.py > <report>
"""
import subprocess, sys, time, os, platform, datetime

EXE = ".lake/build/bin/glsrun"
PRODUCER_DEADLINE = 20.0
KERNEL_DEADLINE = 30.0
FAMILIES = {
    "boxChain": [4, 8, 12, 16, 20, 24, 28, 32],
    "kChain": [4, 16, 32, 64, 128, 256, 512],
    "consis": [4, 8, 12, 16, 20, 24, 28, 32],
    "binTree": [2, 4, 6, 8, 10, 12],
}
VALID = {"boxChain": True, "kChain": True, "consis": False, "binTree": False}

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
        return f"flag: the term was not elaborated ({why})", False
    return f"{max(tc - base, 0):.2f} s", True

os.makedirs("Corpus/out", exist_ok=True)
base_path = "Corpus/out/_base.lean"
open(base_path, "w").write("import GLS.Corpus.Basic\n")
base = min(lean(base_path, 60)[0] for _ in range(3))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.date.today()}.  Loading the imports: {base:.2f} s, taken off the times of the last three columns.")
print(f"Deadlines: producer {PRODUCER_DEADLINE:.0f} s, each check {KERNEL_DEADLINE:.0f} s.  "
      "`flag`: cut off at the deadline, or not elaborated; the column stops there.\n")
print("| family | n | verdict | size of the certificate | producer | the fact with its certificate (a tree): elaborated, and checked by the kernel | the fact with its script | the kernel running the search (`decide +kernel`) |")
print("|---|---|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    cert_on, script_on, dec_on = True, True, True
    for n in ns:
        t, rc, out = timed([EXE, "cert", fam, str(n)], PRODUCER_DEADLINE)
        if t is None:
            print(f"| {fam} | {n} | flag | | flag (> {PRODUCER_DEADLINE:.0f} s) | not run | not run | not run |")
            break
        lines = out.strip().splitlines()
        verdict = lines[0].split(": ")[1].split(",")[0]
        size = lines[0].split("size ")[1]
        prod_ms = lines[1].split(": ")[1]
        cell_c = "not run"
        if cert_on:
            cell_c, cert_on = check(f"Corpus/out/{fam}_{n}.lean", base)
        cell_s = "no script: not a derivation" if not VALID[fam] else "not run"
        if VALID[fam] and script_on:
            cell_s, script_on = check(f"Corpus/out/{fam}_{n}_script.lean", base)
        cell_d = "not run"
        if dec_on:
            path = f"Corpus/out/{fam}_{n}_decide.lean"
            stmt = f"Valid (Corpus.{fam} {n})" if VALID[fam] else f"¬ Valid (Corpus.{fam} {n})"
            open(path, "w").write(
                "import GLS.Corpus.Basic\nopen GLS GLS.Corpus\n\n"
                f"example : {stmt} := by decide +kernel\n")
            td, rcd, outd = lean(path, KERNEL_DEADLINE + base)
            if td is None:
                cell_d, dec_on = f"flag (> {KERNEL_DEADLINE:.0f} s)", False
            elif rcd != 0:
                cell_d, dec_on = "flag: " + outd.strip().splitlines()[0][-80:], False
            else:
                cell_d = f"{max(td - base, 0):.2f} s"
        print(f"| {fam} | {n} | {verdict} | {size} | {prod_ms} ms | {cell_c} | {cell_s} | {cell_d} |", flush=True)
