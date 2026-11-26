#!/usr/bin/env python3
"""Measurements of the certifier of finite phase structures, on the two
families of the corpus that have no derivation.

For each member: the producer of structures (`mallrun model`), and the fact
stated with the structure it found (`lake env lean` on the file written):
elaborated, and checked by the kernel, less the time to load the imports.
Every run is under a deadline.  Run from `calculi/MALL/` after
`lake build mallrun`:  python3 -I Corpus/measure_model.py > <report>
"""
import subprocess, time, os

EXE = ".lake/build/bin/mallrun"
DEADLINE = 30.0
FAMILIES = {"chainBad": [4, 8, 16, 32, 64, 128, 256], "fanBad": [4, 8, 16, 32, 64, 128, 256]}


def timed(cmd, deadline):
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=deadline)
        return time.monotonic() - t0, r.returncode, r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return None, None, ""


os.makedirs("Corpus/out", exist_ok=True)
base_path = "Corpus/out/_base_model.lean"
open(base_path, "w").write("import MALL.Corpus.Basic\nimport MALL.ModelRun\n")
base = min(timed(["lake", "env", "lean", base_path], 60)[0] for _ in range(3))
print(f"Loading the imports: {base:.2f} s, taken off the last column.  Deadline: {DEADLINE:.0f} s each.\n")
print("| family | n | formulas in the sequent | the structure found | the producer | the fact with its structure: elaborated, and checked by the kernel |")
print("|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    for n in ns:
        t, rc, out = timed([EXE, "model", fam, str(n)], DEADLINE)
        if t is None:
            print(f"| {fam} | {n} | {n + 2} | flag (> {DEADLINE:.0f} s) | | not run |")
            break
        lines = out.strip().splitlines()
        found = lines[0].split(": ")[1]
        ms = lines[1].split(": ")[1]
        if found == "none":
            print(f"| {fam} | {n} | {n + 2} | none | {ms} ms | no fact |")
            continue
        tc, rcc, outc = timed(["lake", "env", "lean", f"Corpus/out/{fam}_{n}_model.lean"], DEADLINE + base)
        if tc is None:
            cell = f"flag (> {DEADLINE:.0f} s)"
        elif rcc != 0:
            cell = "flag: " + outc.strip().splitlines()[0][-80:]
        else:
            cell = f"{max(tc - base, 0):.2f} s"
        print(f"| {fam} | {n} | {n + 2} | {found} | {ms} ms | {cell} |", flush=True)
