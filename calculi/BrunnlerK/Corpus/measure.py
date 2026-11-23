#!/usr/bin/env python3
"""Measurements of the Run stage, for the four families of the corpus.

For each member of a family, in growing size:
  * the compiled producer (`ksearch cert`): its verdict, the size of its
    certificate, its time;
  * the fact stated with that certificate (`lake env lean` on the file the
    producer wrote): parsing and elaborating the certificate as a term,
    and the kernel's check of it, less the time to load the imports;
  * for comparison, the kernel running the search itself
    (`by decide +kernel` on `Valid`).
Every run is under a deadline; a run cut off is a flag, and the column
stops there (rules R5, R7 of lean-certify).  Run from `calculi/BrunnlerK/`
after `lake build ksearch`:  python3 Corpus/measure.py > <report>
"""
import subprocess, sys, time, os, platform, datetime

EXE = ".lake/build/bin/ksearch"
PRODUCER_DEADLINE = 10.0
KERNEL_DEADLINE = 30.0
FAMILIES = {
    "boxAnd": [2, 4, 8, 16, 32, 64],
    "nest": [4, 16, 64, 256, 1024],
    "boxOr": [2, 4, 8, 16, 32, 64],
    "late": [2, 4, 6, 8, 10, 12, 14, 16],
}
VALID = {"boxAnd": True, "nest": True, "boxOr": False, "late": True}

def timed(cmd, deadline):
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=deadline)
        return time.monotonic() - t0, r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, None, ""

def lean(path, deadline):
    return timed(["lake", "env", "lean", path], deadline)

os.makedirs("Corpus/out", exist_ok=True)
base_path = "Corpus/out/_base.lean"
open(base_path, "w").write("import BrunnlerK.Corpus.Basic\n")
base = min(lean(base_path, 60)[0] for _ in range(3))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.date.today()}.  Loading the imports: {base:.2f} s, taken off the kernel times.")
print(f"Deadlines: producer {PRODUCER_DEADLINE:.0f} s, each kernel check {KERNEL_DEADLINE:.0f} s.  "
      "`flag`: cut off at the deadline, or not elaborated; the column stops there.\n")
print("| family | n | verdict | size of the certificate | producer | the fact with its certificate: elaborated, and checked by the kernel | the kernel running the search (`decide +kernel`) |")
print("|---|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    cert_on, dec_on = True, True
    for n in ns:
        t, rc, out = timed([EXE, "cert", fam, str(n)], PRODUCER_DEADLINE)
        if t is None:
            print(f"| {fam} | {n} | flag | | flag (> {PRODUCER_DEADLINE:.0f} s) | not run | not run |")
            break
        lines = out.strip().splitlines()
        verdict = lines[0].split(": ")[1].split(",")[0]
        size = lines[0].split("size ")[1]
        prod_ms = lines[1].split(": ")[1]
        cell_c = "not run"
        if cert_on:
            tc, rcc, outc = lean(f"Corpus/out/{fam}_{n}.lean", KERNEL_DEADLINE + base)
            if tc is None:
                cell_c, cert_on = f"flag (> {KERNEL_DEADLINE:.0f} s)", False
            elif rcc != 0:
                why = ("maximum recursion depth" if "maximum recursion" in outc
                       else "deterministic timeout" if "timeout" in outc
                       else outc.strip().splitlines()[0][:60])
                cell_c, cert_on = f"flag: the term was not elaborated ({why})", False
            else:
                cell_c = f"{max(tc - base, 0):.2f} s"
        cell_d = "not run"
        if dec_on:
            path = f"Corpus/out/{fam}_{n}_decide.lean"
            stmt = f"Valid (Corpus.{fam} {n})" if VALID[fam] or (fam == "boxOr" and n < 2) \
                else f"¬ Valid (Corpus.{fam} {n})"
            open(path, "w").write(
                "import BrunnlerK.Corpus.Basic\nopen BrunnlerK BrunnlerK.Corpus\n\n"
                f"example : {stmt} := by decide +kernel\n")
            td, rcd, outd = lean(path, KERNEL_DEADLINE + base)
            if td is None:
                cell_d, dec_on = f"flag (> {KERNEL_DEADLINE:.0f} s)", False
            elif rcd != 0:
                cell_d, dec_on = "error: " + outd.strip().splitlines()[0][:70], False
            else:
                cell_d = f"{max(td - base, 0):.2f} s"
        print(f"| {fam} | {n} | {verdict} | {size} | {prod_ms} ms | {cell_c} | {cell_d} |", flush=True)
