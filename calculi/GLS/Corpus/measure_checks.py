#!/usr/bin/env python3
"""The two checks of GLS, each in two forms, compiled and in the kernel.

A countermodel is checked by `noDerivable.check` (truth by the marks,
`GLS/Table.lean`), proved equal to the definition `Seq.refutedAt`; a tree
of moves by `treeCert.check` (the replay by counts, `GLS/Counts.lean`),
proved equal to the definition `Cert.check`, which writes the sequents
out.  For members of three families this script times all four, compiled
(`glsrun check`) and in the kernel (`lake env lean` on the files that
`glsrun check --files` writes, less the time of the file with the
certificate alone).

Every run has a deadline that ends its process group; Lean runs under a
cap on memory (`-M 8000`); `glsrun check` does not run the list replay
where a side would pass 40 000 000 formulas.  Run from `calculi/GLS/`
after `lake build GLS glsrun`:
    python3 -I Corpus/measure_checks.py [family ...] [n ...] > <report>
With no family: consis, boxChain, lastChain.  With no size: 16, 24, 32,
48, 64.
"""
import subprocess, sys, os, signal, time

EXE = ".lake/build/bin/glsrun"
SIZES = [int(a) for a in sys.argv[1:] if a.isdigit()] or [16, 24, 32, 48, 64]
COMPILED_DEADLINE = 20
KERNEL_DEADLINE = 120
FAMILIES = [a for a in sys.argv[1:] if not a.isdigit()] or ["consis", "boxChain", "lastChain"]

def run(cmd, deadline):
    t0 = time.monotonic()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, time.monotonic() - t0, out, err
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, deadline, "", ""

def micro(text):
    """A figure of `glsrun check`, as text."""
    if text.endswith("µs"):
        us = int(text.split()[0])
        return f"{us} µs" if us < 1000 else f"{us / 1000:.1f} ms" if us < 1000000 else f"{us / 1000000:.2f} s"
    return text

def kernel(path, base):
    code, t, out, err = run(["lake", "env", "lean", "-M", "8000", path], KERNEL_DEADLINE)
    if code is None:
        return f"cut off at {KERNEL_DEADLINE} s"
    if code != 0:
        text = out + err
        return ("stack overflow" if "Stack overflow" in text
                else "over the cap on memory" if "memory" in text
                else "not elaborated: " + text.strip().splitlines()[0][-60:]) + f" (after {t:.0f} s)"
    return f"{max(t - base, 0):.2f} s"

print("| member | certificate | definition, compiled | certifier's check, compiled | definition, kernel | certifier's check, kernel |")
print("|---|---|---|---|---|---|")
for fam in FAMILIES:
    for n in SIZES:
        code, _, out, _ = run([EXE, "check", fam, str(n), f"--deadline={COMPILED_DEADLINE}", "--files"],
                              COMPILED_DEADLINE + 40)
        lines = out.splitlines()
        if not lines:
            print(f"| `{fam} {n}` | no answer | | | | |", flush=True)
            continue
        cert = lines[0].split(": ", 1)[1]
        got = {l.split("\t")[0].split(" (")[0]: l.split("\t")[-1] for l in lines[1:]}
        certifier = got.get("treeCert.check") or got.get("noDerivable.check") or ""
        definition = got.get("Cert.check") or got.get("Seq.refutedAt") or ""
        stem = f"Corpus/out/check/{fam}_{n}"
        base = min(run(["lake", "env", "lean", "-M", "8000", stem + "_base.lean"], KERNEL_DEADLINE)[1]
                   for _ in range(2))
        kd = kernel(stem + "_definition.lean", base)
        kc = kernel(stem + "_certifier.lean", base)
        print(f"| `{fam} {n}` | {cert} | {micro(definition)} | {micro(certifier)} | {kd} | {kc} |", flush=True)
