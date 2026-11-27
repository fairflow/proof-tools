#!/usr/bin/env python3
"""Measurements of the search over sets (`GLS/SetSearch.lean`), for the
four families of the corpus.

For each member of a family, in growing size:
  * the compiled search over sets (`glsrun setcert`): verdict, size, time;
  * the fact "derivable" (or "not derivable") stated with its certificate:
    a tree of moves checked by `setCert`, or a tree checked by
    `noDerivable`;
  * for a derivable sequent, the same tree of moves checked by `treeCert`,
    which gives the derivation in GLS as data;
  * the kernel running the checked decision over sets (`decide +kernel`
    with `derivableDecidableFast`).
Every run is under a deadline that ends its process group, and a cap on
memory of 8 GB; a run cut off is a flag, and the column
stops there.  Run from `calculi/GLS/` after `lake build glsrun
GLS.SetSearch`:  python3 -I Corpus/measure_set.py > <report>
"""
import subprocess, signal, time, os, platform, datetime

EXE = ".lake/build/bin/glsrun"
PRODUCER_DEADLINE = 20.0
KERNEL_DEADLINE = 30.0
FAMILIES = {
    "boxChain": [16, 24, 32, 64, 128, 256],
    "kChain": [16, 64, 128, 256, 512],
    "consis": [16, 24, 32, 64, 128, 256],
    "binTree": [4, 6, 8, 10, 12],
}
VALID = {"boxChain": True, "kChain": True, "consis": False, "binTree": False}

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

def lean(path, deadline):
    return timed(["lake", "env", "lean", "-M", "8000", path], deadline)

def check(path, base):
    tc, rcc, outc = lean(path, KERNEL_DEADLINE + base)
    if tc is None:
        return f"flag (> {KERNEL_DEADLINE:.0f} s)", False
    if rcc != 0:
        why = ("maximum recursion depth" if "maximum recursion" in outc
               else "deterministic timeout" if "timeout" in outc
               else outc.strip().splitlines()[0][-80:])
        return f"flag: not elaborated ({why})", False
    return f"{max(tc - base, 0):.2f} s", True

os.makedirs("Corpus/out", exist_ok=True)
base_path = "Corpus/out/_base_set.lean"
open(base_path, "w").write("import GLS.Corpus.Basic\nimport GLS.SetSearch\n")
base = min(lean(base_path, 60)[0] for _ in range(3))

print(f"Machine: {platform.machine()}, {platform.platform()}.  "
      f"Date: {datetime.date.today()}.  Loading the imports: {base:.2f} s, taken off the times of the last three columns.")
print(f"Deadlines: producer {PRODUCER_DEADLINE:.0f} s, each check {KERNEL_DEADLINE:.0f} s.\n")
print("| family | n | verdict | size of the certificate | the search over sets | the fact with its certificate, by `setCert` or `noDerivable` | the same tree of moves by `treeCert`: the derivation as data | the kernel running the decision over sets (`decide +kernel`) |")
print("|---|---|---|---|---|---|---|---|")
for fam, ns in FAMILIES.items():
    set_on, tree_on, dec_on = True, True, True
    for n in ns:
        t, rc, out = timed([EXE, "setcert", fam, str(n)], PRODUCER_DEADLINE)
        if t is None:
            print(f"| {fam} | {n} | flag | | flag (> {PRODUCER_DEADLINE:.0f} s) | not run | not run | not run |")
            break
        lines = out.strip().splitlines()
        verdict = lines[0].split(": ")[1].split(",")[0]
        size = lines[0].split("size ")[1]
        prod_ms = lines[1].split(": ")[1]
        cell_s = "not run"
        if set_on:
            cell_s, set_on = check(f"Corpus/out/{fam}_{n}_set.lean", base)
        cell_t = "not a derivation" if not VALID[fam] else "not run"
        if VALID[fam] and tree_on:
            cell_t, tree_on = check(f"Corpus/out/{fam}_{n}_settree.lean", base)
        cell_d = "not run"
        if dec_on:
            path = f"Corpus/out/{fam}_{n}_setdecide.lean"
            stmt = f"Derivable (Corpus.{fam} {n})" if VALID[fam] else f"¬ Derivable (Corpus.{fam} {n})"
            open(path, "w").write(
                "import GLS.Corpus.Basic\nimport GLS.SetSearch\nopen GLS GLS.Corpus\n\n"
                "instance (s : Seq) : Decidable (Derivable s) := derivableDecidableFast s\n\n"
                f"example : {stmt} := by decide +kernel\n")
            td, rcd, outd = lean(path, KERNEL_DEADLINE + base)
            if td is None:
                cell_d, dec_on = f"flag (> {KERNEL_DEADLINE:.0f} s)", False
            elif rcd != 0:
                cell_d, dec_on = "flag: " + outd.strip().splitlines()[0][-80:], False
            else:
                cell_d = f"{max(td - base, 0):.2f} s"
        print(f"| {fam} | {n} | {verdict} | {size} | {prod_ms} ms | {cell_s} | {cell_t} | {cell_d} |", flush=True)
