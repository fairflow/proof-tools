/-
The driver of the measurements of the saturated sets: the producer on one
member of the family "the chain with its last link missing",

    · ; a₀, a₀ ⊸ a₁, …, aₙ₋₂ ⊸ aₙ₋₁ ⟹ aₙ      (n formulas in the linear zone),

with the times of its parts, and the fact file that states the result
with the set, for the kernel to check.

    lake env lean --run Corpus/SatMain.lean <n> <first|shortest> [<file>]

Code: nothing here is trusted.  `Corpus/measure_sat.py` runs it under a
deadline, and compiles it first where it can.
-/
import DILL.Refute

open DILL DILL.Refute

/-- The chain with its last link missing. -/
def chainBad (n : Nat) : Seq :=
  [] ⨾ (.atom 0 :: (List.range (n - 1)).map fun i => .atom i ⊸ .atom (i + 1)) ⟹ .atom n

/-- The fact, with its set, as a Lean file. -/
def factFile (j : Seq) (D : List Seq) : String :=
  "import DILL.SatRun\nopen DILL\n" ++
  "abbrev p : Form := .atom 0\nabbrev q : Form := .atom 1\n" ++
  "abbrev r : Form := .atom 2\nabbrev s : Form := .atom 3\n" ++
  "set_option maxRecDepth 100000 in\n" ++
  "theorem fact : ¬ Nonempty (CF (" ++ srcSeq j ++ ")) :=\n  noCFBySet.verdict _\n    [" ++
  ",\n     ".intercalate (D.map srcSeq) ++ "]\n"

def main (args : List String) : IO UInt32 := do
  let (ns, chs, out) ← match args with
    | [ns, chs] => pure (ns, chs, none)
    | [ns, chs, out] => pure (ns, chs, some out)
    | _ => do
      IO.eprintln "usage: SatMain <n> <first|shortest> [<file>]"
      return 2
  let n := ns.toNat!
  let ch : Choice := if chs == "shortest" then .shortest else .first
  let j := chainBad n
  let t₀ ← IO.monoMsNow
  let (b, st) := search j.lin j.goal
  let settled := st.memo.size
  let nos := (st.memo.toList.filter fun kv => !kv.2).length
  IO.println s!"n={n} formulas={j.lin.length + 1} answer={b} settled={settled} no={nos}"
  let t₁ ← IO.monoMsNow
  if b then
    IO.println "verdict=none"
    return 1
  let D := setOf st ch j
  IO.println s!"set={D.length} longest={(D.map (·.lin.length)).foldl max 0}"
  let t₂ ← IO.monoMsNow
  let ok := refutedBy D j
  IO.println s!"check={ok}"
  let t₃ ← IO.monoMsNow
  IO.println s!"search_ms={t₁ - t₀} closure_ms={t₂ - t₁} check_ms={t₃ - t₂}"
  if !ok then
    IO.println "verdict=defect"
    return 3
  if let some f := out then IO.FS.writeFile f (factFile j D)
  IO.println "verdict=refuted"
  return 0
