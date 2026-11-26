#!/usr/bin/env python3
"""`mallrun prove` on every entry of the corpus.

Each entry is given to the command as text, three times: in the source's
notation (`showSeq`), as Lean source (`srcForms`) and with the signs of a
keyboard (`asciiSeq`), as `mallrun corpus` prints them.  The exit code is
compared with the status the corpus records: 0 for an entry recorded
derivable, 1 for one recorded not derivable; and the three answers are
compared with one another.  With `--elaborate`, the file the command
prints for each entry is written to `Corpus/out/prove/<name>.lean` and
elaborated (`lake env lean -M 8000`, under a deadline that ends the whole
process group): the kernel then checks its certificate.

Run from `calculi/MALL/` after `lake build mallrun`:
    python3 -I Corpus/prove_corpus.py [--elaborate]
Exit code 0 if nothing disagrees and nothing fails to elaborate.
"""
import subprocess, sys, os, signal

EXE = ".lake/build/bin/mallrun"
ELABORATE = "--elaborate" in sys.argv
DEADLINE = 60.0
WORD = {0: "derivable", 1: "not derivable", 2: "not read", 3: "flag"}


def run(cmd, deadline=DEADLINE):
    """Run in a process group of its own; at the deadline the group is ended,
    so that a `lean` started by `lake` does not outlive it."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, out, err
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, "", "cut off at the deadline"


code, out, _ = run([EXE, "corpus"])
entries = [line.split("\t") for line in out.splitlines()]
if ELABORATE:
    os.makedirs("Corpus/out/prove", exist_ok=True)

counts, kinds, disagree, bad = {}, {}, 0, 0
print("| entry | recorded | from the source's notation | from Lean source | from the signs of a keyboard | first line | certificate |" +
      (" elaborated |" if ELABORATE else ""))
print("|---|---|---|---|---|---|---|" + ("---|" if ELABORATE else ""))
for name, status, shown, src, ascii in entries:
    want = 0 if status == "derivable" else 1
    c1, o1, _ = run([EXE, "prove", shown])
    c2, o2, _ = run([EXE, "prove", src])
    c3, o3, _ = run([EXE, "prove", ascii])
    first = o1.splitlines()[0] if o1 else ""
    kind = ("a tree of moves" if "def tree" in o1 else
            "a cyclic phase structure" if "def countermodel : ZModel" in o1 else
            "a saturated set" if "def refutation" in o1 else "none")
    ok = c1 == want and c2 == want and c3 == want and o1 == o2 == o3
    if not ok:
        disagree += 1
    counts[WORD.get(c1, "cut off")] = counts.get(WORD.get(c1, "cut off"), 0) + 1
    kinds[kind] = kinds.get(kind, 0) + 1
    row = (f"| `{name}` | {status} | {WORD.get(c1, 'cut off')} | {WORD.get(c2, 'cut off')} | "
           f"{WORD.get(c3, 'cut off')} | `{first}` | {kind} |")
    if ELABORATE:
        path = f"Corpus/out/prove/{name.replace(chr(39), '_')}.lean"
        with open(path, "w") as f:
            f.write(o1)
        ce, oe, ee = run(["lake", "env", "lean", "-M", "8000", path])
        good = ce == 0 and "error" not in oe and "sorry" not in oe
        if not good:
            bad += 1
        row += " yes |" if good else f" NO: {(oe + ee).strip().splitlines()[:1]} |"
    print(row + ("" if ok else " DISAGREES"), flush=True)

print()
print(f"{len(entries)} entries; by verdict: " +
      ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) +
      "; by certificate: " + ", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) +
      f"; disagreeing with the recorded status, or the three texts answered differently: {disagree}" +
      (f"; files not elaborated: {bad}" if ELABORATE else ""))
sys.exit(0 if disagree == 0 and bad == 0 else 1)
