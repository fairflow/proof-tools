#!/usr/bin/env python3
"""`ksearch prove` on every entry of the corpus.

Each entry is given to the command as text, three times: in the source's
notation (`NSeq.show`), as Lean source (`NSeq.src`) and with the signs of
a keyboard (`NSeq.ascii`), as `ksearch corpus` prints them.  The exit
code is compared with the status the corpus records: 0 for an entry
recorded valid, 1 for one recorded not valid; and the three answers are
compared with one another.  A flag (exit code 3) states nothing, so it
agrees with either status: flagged entries are not counted as
disagreeing, and are named at the end.  With `--elaborate`, the file the
command prints for each entry is written to `Corpus/out/prove/<name>.lean`
and elaborated (`lake env lean`, under a cap on memory and a deadline):
the kernel then checks its certificate.

K has one kind of certificate for each verdict (a tree of moves; a finite
tree against validity), so the counts by verdict are the counts by kind.
Each command runs in a process group of its own, and the group is ended
at the deadline.

Run from `calculi/BrunnlerK/` after `lake build ksearch`:
    python3 Corpus/prove_corpus.py [--elaborate]
Exit code 0 if nothing disagrees and nothing fails to elaborate.
"""
import subprocess, sys, os, signal

EXE = ".lake/build/bin/ksearch"
ELABORATE = "--elaborate" in sys.argv
DEADLINE = 60.0
WORD = {0: "derivable", 1: "not derivable", 2: "not read", 3: "flag"}

def run(cmd, deadline=DEADLINE):
    """Run under a deadline; at the deadline the whole process group ends
    (`subprocess.run(timeout=…)` would end `lake` and leave `lean`)."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
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

counts, disagree, bad, flagged = {}, 0, 0, []
print("| entry | recorded | from the source's notation | from Lean source | from the signs of a keyboard | first line |" +
      (" elaborated |" if ELABORATE else ""))
print("|---|---|---|---|---|---|" + ("---|" if ELABORATE else ""))
for name, status, shown, src, ascii in entries:
    want = 0 if status == "valid" else 1
    c1, o1, _ = run([EXE, "prove", shown])
    c2, o2, _ = run([EXE, "prove", src])
    c3, o3, _ = run([EXE, "prove", ascii])
    first = o1.splitlines()[0] if o1 else ""
    ok = all(c in (want, 3) for c in (c1, c2, c3)) and o1 == o2 == o3
    if 3 in (c1, c2, c3):
        flagged.append(name)
    if not ok:
        disagree += 1
    counts[WORD.get(c1, "cut off")] = counts.get(WORD.get(c1, "cut off"), 0) + 1
    row = f"| `{name}` | {status} | {WORD.get(c1, 'cut off')} | {WORD.get(c2, 'cut off')} | {WORD.get(c3, 'cut off')} | `{first}` |"
    if ELABORATE:
        if c1 in (0, 1):
            path = f"Corpus/out/prove/{name}.lean"
            with open(path, "w") as f:
                f.write(o1)
            ce, oe, ee = run(["lake", "env", "lean", "-M", "8000", path])
            good = ce == 0 and "error" not in oe and "sorry" not in oe
            if not good:
                bad += 1
            row += " yes |" if good else f" NO: {(oe + ee).strip().splitlines()[:1]} |"
        else:
            row += " no fact to elaborate |"
    print(row + ("" if ok else " DISAGREES"))

print()
print(f"{len(entries)} entries; by verdict: " +
      ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) +
      f"; disagreeing with the recorded status, or the three texts answered differently: {disagree}" +
      f"; flagged: {len(flagged)}" + (f" ({', '.join(flagged)})" if flagged else "") +
      (f"; files not elaborated: {bad}" if ELABORATE else ""))
sys.exit(0 if disagree == 0 and bad == 0 else 1)
