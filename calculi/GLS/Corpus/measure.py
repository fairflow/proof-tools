#!/usr/bin/env python3
"""Measurements of the Run stage, for the five families of the corpus.

For each member of a family, in growing size:
  * the compiled search (`glsrun cert`): its verdict, the size of its
    certificate, its time;
  * the fact stated with that certificate (`lake env lean` on a file the
    program wrote), less the time to load the imports: for a derivation
    the tree of moves by `treeCert` (the derivation as data), the same
    tree by `setCert` (the proposition), and its script by `scriptCert`;
    for a sequent that is not derivable, the tree of worlds by
    `noDerivable`;
  * the kernel running the search itself (`by decide +kernel` on `Valid`).
Every run is under a deadline that ends its process group, and a cap on
memory (8 GB for the program, `-M 4000` for Lean); a run cut off is a
flag, and the column stops there (rules R5, R7 of lean-certify).  Run
from `calculi/GLS/` after `lake build GLS glsrun`:
    python3 -I Corpus/measure.py [family ...] > <report>
"""
import subprocess, signal, sys, time, os, platform, datetime

EXE = ".lake/build/bin/glsrun"
PRODUCER_DEADLINE = 20.0
KERNEL_DEADLINE = 60.0
FAMILIES = {
    "boxChain": [16, 32, 64, 128, 256, 512],
    "lastChain": [16, 32, 64, 128, 256, 512],
    "kChain": [16, 32, 64, 128, 256, 512],
    "consis": [16, 32, 64, 128, 256, 512],
    "binTree": [4, 6, 8, 10, 12],
}
VALID = {"boxChain": True, "lastChain": True, "kChain": True, "consis": False, "binTree": False}
ASKED = [a for a in sys.argv[1:] if a in FAMILIES]
if ASKED:
    FAMILIES = {f: FAMILIES[f] for f in ASKED}

def timed(cmd, deadline, cap_mb=8000):
    """Run under a deadline and a cap on memory.  At the deadline, or when
    the process holds more than the cap, its whole process group ends."""
    t0 = time.monotonic()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    while True:
        try:
            out, err = p.communicate(timeout=0.2)
            return time.monotonic() - t0, p.returncode, out + err
        except subprocess.TimeoutExpired:
            rss = subprocess.run(["ps", "-o", "rss=", "-p", str(p.pid)],
                                 capture_output=True, text=True).stdout.strip()
            over = rss.isdigit() and int(rss) > cap_mb * 1024
            if over or time.monotonic() - t0 > deadline:
                os.killpg(p.pid, signal.SIGKILL)
                p.communicate()
                return None, None, "over the cap on memory" if over else ""

def micro(text):
    """A figure of `glsrun check`, as text."""
    if text.endswith("µs"):
        us = int(text.split()[0])
        return f"{us} µs" if us < 1000 else f"{us / 1000:.1f} ms" if us < 1000000 else f"{us / 1000000:.2f} s"
    return text

def lean(path, deadline):
    return timed(["lake", "env", "lean", "-M", "4000", path], deadline)

def check(path, base):
    """One fact file: its time less the imports, or why it is a flag."""
    tc, rcc, outc = lean(path, KERNEL_DEADLINE + base)
    if tc is None:
        return f"flag (> {KERNEL_DEADLINE:.0f} s)", False
    if rcc != 0:
        why = ("over the cap on memory, 4 GB" if "excessive memory" in outc
               else "maximum recursion depth" if "maximum recursion" in outc
               else "deterministic timeout" if "timeout" in outc
               else outc.strip().splitlines()[0][-80:])
        return f"flag: not checked ({why})", False
    return f"{max(tc - base, 0):.2f} s", True

os.makedirs("Corpus/out", exist_ok=True)
base_path = "Corpus/out/_base.lean"
open(base_path, "w").write("import GLS.Corpus.Basic\nimport GLS.SetSearch\n")
base = min(lean(base_path, 60)[0] for _ in range(3))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.date.today()}.  Loading the imports: {base:.2f} s, taken off the times of the kernel's columns.")
print(f"Deadlines: the search {PRODUCER_DEADLINE:.0f} s, each check {KERNEL_DEADLINE:.0f} s.  "
      "`flag`: cut off at the deadline, or not elaborated; the column stops there.\n")
print("| family | n | verdict | size of the certificate | the search, compiled | `treeCert` or `noDerivable`, compiled | `scriptCert`, compiled | the tree by `treeCert` or `noDerivable`, kernel | the tree of moves by `setCert`, kernel | the script by `scriptCert`, kernel | the kernel running the search (`decide +kernel`) |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    cert_on, set_on, script_on, dec_on = True, True, True, True
    for n in ns:
        t, rc, out = timed([EXE, "cert", fam, str(n)], PRODUCER_DEADLINE)
        if t is None or rc != 0:
            print(f"| {fam} | {n} | flag | | flag (> {PRODUCER_DEADLINE:.0f} s, or the cap on memory) | not run | not run | not run | not run | not run | not run |")
            break
        lines = out.strip().splitlines()
        verdict = lines[0].split(": ")[1].split(",")[0]
        size = lines[0].split("size ")[1]
        prod_ms = lines[1].split(": ")[1]
        # the certifiers' checks compiled: `glsrun check` times each function
        _, _, outk = timed([EXE, "check", fam, str(n)], PRODUCER_DEADLINE)
        got = {l.split("\t")[0].split(" (")[0]: micro(l.split("\t")[-1]) for l in (outk or "").splitlines()[1:]}
        comp_c = got.get("treeCert.check") or got.get("noDerivable.check") or "no answer"
        comp_s = got.get("scriptCert.check") or ("not a derivation" if not VALID[fam] else "no answer")
        cell_c = "not run"
        if cert_on:
            cell_c, cert_on = check(f"Corpus/out/{fam}_{n}.lean", base)
        none = "not a derivation"
        cell_t = none if not VALID[fam] else "not run"
        if VALID[fam] and set_on:
            cell_t, set_on = check(f"Corpus/out/{fam}_{n}_set.lean", base)
        cell_s = none if not VALID[fam] else "not run"
        if VALID[fam] and script_on:
            cell_s, script_on = check(f"Corpus/out/{fam}_{n}_script.lean", base)
        cell_d = "not run"
        if dec_on:
            path = f"Corpus/out/{fam}_{n}_decide.lean"
            stmt = f"Valid (Corpus.{fam} {n})" if VALID[fam] else f"¬ Valid (Corpus.{fam} {n})"
            open(path, "w").write(
                "import GLS.Corpus.Basic\nopen GLS GLS.Corpus\n\n"
                "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n"
                f"example : {stmt} := by decide +kernel\n")
            td, rcd, outd = lean(path, KERNEL_DEADLINE + base)
            if td is None:
                cell_d, dec_on = f"flag (> {KERNEL_DEADLINE:.0f} s)", False
            elif rcd != 0:
                cell_d, dec_on = "flag: " + ("over the cap on memory, 4 GB" if "excessive memory" in outd
                                             else outd.strip().splitlines()[0][-80:]), False
            else:
                cell_d = f"{max(td - base, 0):.2f} s"
        print(f"| {fam} | {n} | {verdict} | {size} | {prod_ms} ms | {comp_c} | {comp_s} | {cell_c} | {cell_t} | {cell_s} | {cell_d} |", flush=True)
