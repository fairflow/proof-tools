# The experiments of 2026-11-27 (method note 23)

The scripts that found why two checks were slow in the kernel, kept as
they were run. Each writes Lean files into `Corpus/out/exp/` (ignored)
and elaborates them one at a time under a cap on memory and a deadline
on the process group (`h.py`). Run from `calculi/DILL/` after `lake
build DILL dillrun`, as `python3 -I Corpus/experiments/<name>.py <sizes>`.
The figures they gave are in `campaign/measurements-sat.md` and
`campaign/measurements.md`, "The cost of the check".

| script | what it shows |
|---|---|
| `e1.py`, `e2.py` | the check stated of `refutedBy` and through the certifier: the same in the kernel (`e2.py V1 8000`, `e2.py V2 8000`: the set of 200 at the old cap) |
| `e3.py` | the two facts that use `checked`: the elaborator computes the check again where `checked` is stated of `refutedBy` |
| `e4.py` | a copy of the definition's check that counts: divisions, questions, pairs of sequents, zones compared |
| `b1.py` to `b4.py` | what a step costs the kernel: lists, arithmetic, three equalities of formulas |
| `p1.py` to `p3.py`, `proto.lean.txt` | the tree for the sets, as a prototype with no proofs: its answer beside the definition's, its parts timed, its depth varied |
| `t1.py`, `t2.py` | the fact with the tree of `chain n`; the part named in the zone's order |
| `s1.py` | the file `dillrun prove` prints for a set, elaborated |

They run against the library as it is now. The "before" figures of the
tree check (`t1.py` on `step` with `Move.rule`) are not reproduced by
them since `step` runs `Move.ruleF`; `e1.py` to `e4.py` are of
`refutedBy`, which is unchanged, and still give the "before" of the
sets. `e2.py` asks for `-M 8000` on purpose; nothing else passes 4000.
