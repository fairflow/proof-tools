#!/usr/bin/env python3
"""`ksearch prove` beyond the corpus: members of the families that grow.

For each member: the text (`ksearch show <family> <n>`, or written here),
the command's answer and its time, the size of the printed file, and the
file elaborated (`lake env lean -M 8000`, under a deadline) with its
time.  It is how the size was looked for at which Lean no longer checks
what the search prints.

The members are named `<family>:<n>`.  The families of the corpus
(`boxAnd`, `nest`, `boxOr`, `late`) and one written here, which the
corpus has not: `tree:<k>`, the formula F_k with F_0 = p and
F_(k+1) = □F_k ∨ □F_k.  It is not valid, and its countermodel is the
full binary tree of depth k: 2^(k+1) - 1 nodes.  It is the "no" side
made to grow (the countermodel of `boxOr n` has n + 1 nodes only).
And `chain:<n>`, the formula □ⁿp: not valid, its countermodel a chain of
n + 1 nodes; the "no" side made deep.

Run from `calculi/BrunnlerK/` after `lake build ksearch`:
    python3 Corpus/prove_families.py [--deadline=S] [--lean-deadline=S] <family>:<n> ...
With no member named, a default list.  Each command runs in a process
group of its own, and the group is ended at the deadline.  Exit code 0 if
every file was elaborated but those whose first line says that the answer
rests on the program's check.
"""
import subprocess, sys, os, signal, time

EXE = ".lake/build/bin/ksearch"
OUT = "Corpus/out/families"
WORD = {0: "derivable", 1: "not derivable", 2: "not read", 3: "flag"}
DEFAULT = ["boxAnd:16", "boxAnd:64", "nest:64", "nest:256", "boxOr:16", "late:16",
           "tree:4", "tree:8"]

def option(name, default):
    for a in sys.argv[1:]:
        if a.startswith(f"--{name}="):
            return float(a.split("=", 1)[1])
    return default

DEADLINE = option("deadline", 60.0)          # for `ksearch prove`, seconds
LEAN_DEADLINE = option("lean-deadline", 300.0)

def run(cmd, deadline):
    """Run under a deadline; at the deadline the whole process group ends
    (`subprocess.run(timeout=…)` would end `lake` and leave `lean`)."""
    t0 = time.time()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, out, err, time.time() - t0
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, "", "cut off at the deadline", time.time() - t0

def tree(k):
    f = "p"
    for _ in range(k):
        f = f"([]{f} | []{f})"
    return f

def text_of(fam, n):
    if fam == "tree":
        return tree(n)
    if fam == "chain":
        return "[]" * n + "p"
    code, out, err, _ = run([EXE, "show", fam, str(n)], 60.0)
    if code != 0:
        sys.exit(f"{fam} {n}: {err.strip()}")
    return out.strip()

members = [a for a in sys.argv[1:] if not a.startswith("--")] or DEFAULT
os.makedirs(OUT, exist_ok=True)
print(f"| member | answer | `ksearch prove`, s | the file, bytes | elaborated (`-M 8000`, {LEAN_DEADLINE:.0f} s) | s |")
print("|---|---|---|---|---|---|")
bad = 0
for m in members:
    fam, n = m.split(":")
    text = text_of(fam, int(n))
    try:
        code, out, err, t = run([EXE, "prove", f"--deadline={int(DEADLINE)}", text], DEADLINE + 5)
    except OSError as e:
        # a text longer than the operating system gives a command line
        print(f"| `{fam} {n}` | not run: a text of {len(text.encode())} bytes, {e.strerror} | | | no file | |", flush=True)
        continue
    word = WORD.get(code, "cut off")
    first = out.splitlines()[0] if out else ""
    if code in (0, 1) and "on the program's check" in first:
        word += ", on the program's check"
    row = f"| `{fam} {n}` | {word} | {t:.2f} | {len(out.encode())} |"
    if code in (0, 1):
        path = f"{OUT}/{fam}_{n}.lean"
        with open(path, "w") as f:
            f.write(out)
        ce, oe, ee, te = run(["lake", "env", "lean", "-M", "8000", path], LEAN_DEADLINE)
        if ce == 0 and "error" not in oe and "sorry" not in oe:
            row += f" yes | {te:.1f} |"
        else:
            # a file the first line says rests on the program's check is
            # expected not to be elaborated here
            bad += 0 if "on the program's check" in word else 1
            why = "cut off at the deadline" if ce is None else ((oe + ee).strip().splitlines() or ["no output"])[0][:160]
            row += f" NO: {why} | {te:.1f} |"
    else:
        row += " no file | |"
    print(row, flush=True)
sys.exit(0 if bad == 0 else 1)
