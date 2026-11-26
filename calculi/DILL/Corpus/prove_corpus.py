#!/usr/bin/env python3
"""`dillrun prove` on every entry of the corpus.

Each entry is given to the command as text, three times: in the source's
notation (`showSeq`), as Lean source (`seqSrc`) and with the signs of a
keyboard (`Parse.asciiSeq`), as `dillrun corpus` prints them.  The exit
code is compared with the status the corpus records, and the three
answers with one another.  The search has a budget and the saturated
sets cover a part of the sequents only, so `flag` (exit code 3) is an
answer for an entry of either status: it disagrees with nothing, and it
is counted and named.  What disagrees: `derivable` (0) for an entry
recorded not derivable, `not derivable` (1) for one recorded derivable,
a text not read (2), a run cut off, or three texts answered differently.

Also: two texts that are not sequents, each to be refused with exit code
2, the report with its mark on the error stream and nothing on the
standard output; and a sequent on which the search for a saturated set
does not end in a minute, to be answered `flag` at a deadline of 1 s.

With `--elaborate`, the file the command prints for each entry is
written to `Corpus/out/prove/<name>.lean` and elaborated (`lake env
lean`, under a cap on memory and a deadline that ends the whole process
group): the kernel then checks its certificate.  A flag prints no fact,
and its file of comments is elaborated all the same.  Then two files
are altered and must be refused: a tree of moves replaced by the one
move `init`, and a saturated set with its first member left out.

Run from `calculi/DILL/` after `lake build DILL dillrun`:
    python3 -I Corpus/prove_corpus.py [--elaborate]
Exit code 0 if nothing disagrees, every file elaborates and both altered
files are refused.
"""
import subprocess, sys, os, signal, re

EXE = ".lake/build/bin/dillrun"
ELABORATE = "--elaborate" in sys.argv
DEADLINE = 120.0
WORD = {0: "derivable", 1: "not derivable", 2: "not read", 3: "flag"}

def run(cmd, deadline=DEADLINE):
    """Exit code, standard output, error stream.  At the deadline the whole
    process group is ended: ending `lake` alone leaves `lean` running."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    try:
        out, err = p.communicate(timeout=deadline)
        return p.returncode, out, err
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None, "", "cut off at the deadline"

def elaborate(path):
    code, out, err = run(["lake", "env", "lean", "-M", "8000", path])
    good = code == 0 and "error" not in out and "sorry" not in out
    return good, (out + err).strip().splitlines()[:1]

code, out, _ = run([EXE, "corpus"])
entries = [line.split("\t") for line in out.splitlines()]
if code != 0 or not entries:
    sys.exit(f"`{EXE} corpus` gave nothing: build it first (lake build DILL dillrun)")
if ELABORATE:
    os.makedirs("Corpus/out/prove", exist_ok=True)

counts, flags, disagree, bad = {}, [], 0, 0
files = {}
print("| entry | recorded | from the source's notation | from Lean source | from the signs of a keyboard | first line |" +
      (" elaborated |" if ELABORATE else ""))
print("|---|---|---|---|---|---|" + ("---|" if ELABORATE else ""))
for name, status, shown, src, ascii in entries:
    against = 1 if status == "derivable" else 0
    c1, o1, _ = run([EXE, "prove", shown])
    c2, o2, _ = run([EXE, "prove", src])
    c3, o3, _ = run([EXE, "prove", ascii])
    first = o1.splitlines()[0] if o1 else ""
    ok = c1 in (0, 1, 3) and c1 != against and c1 == c2 == c3 and o1 == o2 == o3
    if not ok:
        disagree += 1
    word = WORD.get(c1, "cut off")
    counts[word] = counts.get(word, 0) + 1
    if c1 == 3:
        flags.append(f"`{name}` ({status})")
    row = f"| `{name}` | {status} | {word} | {WORD.get(c2, 'cut off')} | {WORD.get(c3, 'cut off')} | `{first}` |"
    if ELABORATE:
        path = f"Corpus/out/prove/{name}.lean"
        with open(path, "w") as f:
            f.write(o1)
        files[name] = (c1, o1)
        good, said = elaborate(path)
        if not good:
            bad += 1
        row += " yes |" if good else f" NO: {said} |"
    print(row + ("" if ok else " DISAGREES"))

print()
print(f"{len(entries)} entries; by verdict: " +
      ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) +
      f"; disagreeing with the recorded status, or the three texts answered differently: {disagree}" +
      (f"; files not elaborated: {bad}" if ELABORATE else ""))
print("Flags: " + (", ".join(flags) if flags else "none") + ".")

# Texts that are not sequents.
wrong = 0
for text, n in [("p, => q", 4), ("p -o", 5)]:
    c, o, e = run([EXE, "prove", text])
    lines = e.splitlines()
    good = (c == 2 and o == "" and len(lines) == 3 and f"at character {n}:" in lines[0]
            and lines[1] == "  " + text and lines[2] == "  " + " " * (n - 1) + "^")
    if not good:
        wrong += 1
    print(f"Not a sequent, `{text}`: " +
          ("refused, exit code 2, the mark under character " + str(n) + ", nothing on the standard output."
           if good else f"NOT AS EXPECTED: exit code {c}, standard output {o!r}, error stream {e!r}"))

# The deadline: the search for a set on 24 equal atoms against 25.
import time
text = ", ".join(["p"] * 24) + " => " + " * ".join(["p"] * 25)
t = time.time()
c, o, e = run([EXE, "prove", "--deadline=1", text], deadline=20.0)
took = time.time() - t
good = c == 3 and o.startswith("-- flag: ") and "No answer within 1 s" in o
if not good:
    wrong += 1
print("The deadline, `p, …, p => p * … * p` (24 against 25) with `--deadline=1`: " +
      (f"flag, exit code 3, after {took:.1f} s." if good else f"NOT AS EXPECTED: exit code {c} after {took:.1f} s"))

# Altered certificates.
unrefused = 0
if ELABORATE:
    def alter(kind, pick, change):
        global unrefused
        for name, (c, text) in files.items():
            new = pick(c, text) and change(text)
            if new and new != text:
                path = f"Corpus/out/prove/{name}_altered.lean"
                with open(path, "w") as f:
                    f.write(new)
                good, said = elaborate(path)
                if good:
                    unrefused += 1
                print(f"Altered, `{name}` ({kind}): " +
                      (f"NOT REFUSED" if good else f"refused: {said}"))
                return
        unrefused += 1
        print(f"Altered ({kind}): NO FILE TO ALTER")
    # A tree of more than one move, replaced by the one move `init`.
    alter("the tree of moves replaced by `.mk .init []`",
          lambda c, t: c == 0 and "treeCert.verdict _ (.mk .init [])" not in t,
          lambda t: re.sub(r"treeCert\.verdict _ \(.*\)\n", "treeCert.verdict _ (.mk .init [])\n", t))
    # A saturated set of two members at least, without its first.
    alter("the saturated set without its first member",
          lambda c, t: c == 1 and re.search(r"saturated : List Seq :=\n  \[.*,\n", t),
          lambda t: re.sub(r"(saturated : List Seq :=\n  \[).*,\n   ", r"\1", t, count=1))

sys.exit(0 if disagree == 0 and bad == 0 and wrong == 0 and unrefused == 0 else 1)
