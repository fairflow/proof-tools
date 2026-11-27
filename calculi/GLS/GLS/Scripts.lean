/-
The replay of a script with its goals kept by counts: the check of the
certifier `scriptCert` (`GLS/Run.lean`).

A script is a list of lines, each a move at one of the open goals.  The
library's `derives` runs it on an attempt, a partial derivation that
holds every sequent written out (`ProofTools.Explore.Certify`); in GLS
those sequents have `2ⁿ` formulas after `n` nested GLR.

Two steps here.  First, for any proof system: what `derives` computes is
what a run on the bare list of open goals computes, where a line replaces
the goal it names by the premises of its move (`derives_eq_goalsDone`;
from the library's `Att.moveAt_ok`, `Att.moveAt_error`, `Att.moveAt_inr`).
Then, for GLS: that run with each goal by counts and `countStep` for
`step` gives the same answer, by `countStep_rep`.

    s.scriptCheck ls = derives S s ls                   (scriptCheck_eq, S29)

Theory file: it ends with its bound on axioms.
-/
import GLS.Counts
import ProofTools.Explore.Certify

namespace GLS

open ProofTools ProofTools.Explore

/-! ## A script on a list of goals, for any proof system -/

section Goals

variable {S : ProofSystem}

/-- **One line on a list of goals**: the move at the goal the line names,
whose premises take its place; nothing if there is no such goal or the
move does not apply. -/
def goalsLine {σ : Type} (step : S.Move → σ → Option (List σ)) (gs : List σ) (l : Line S) :
    Option (List σ) :=
  match gs[l.goal]? with
  | none => none
  | some g =>
    match step l.move g with
    | none => none
    | some ps => some (gs.take l.goal ++ ps ++ gs.drop (l.goal + 1))

/-- **A script on a list of goals**: the goals left, or nothing if a line
failed. -/
def goalsRun {σ : Type} (step : S.Move → σ → Option (List σ)) : List σ → Script S → Option (List σ)
  | gs, [] => some gs
  | gs, l :: ls =>
    match goalsLine step gs l with
    | none => none
    | some gs' => goalsRun step gs' ls

/-- **The script runs to the end and leaves no goal.** -/
def goalsDone {σ : Type} (step : S.Move → σ → Option (List σ)) (gs : List σ) (ls : Script S) :
    Bool :=
  match goalsRun step gs ls with
  | some [] => true
  | _ => false

/-- The step of a proof system, with nothing for a move that does not
apply. -/
def stepOpt (S : ProofSystem) (m : S.Move) (j : S.Judg) : Option (List S.Judg) :=
  match S.step m j with
  | .ok ps => some ps
  | .error _ => none

/-- What one line does to the open goals of an attempt. -/
theorem Att.step_goals {j : S.Judg} (d : Att S true j) (l : Line S) :
    (∃ d', d.step l = .ok d' ∧ goalsLine (stepOpt S) d.goals l = some d'.goals) ∨
    (∃ e, d.step l = .error e ∧ goalsLine (stepOpt S) d.goals l = none) := by
  unfold Att.step
  cases h : d.moveAt l.move l.goal with
  | inl r =>
    cases r with
    | ok d' =>
      obtain ⟨g, ps, hg, hs, hgoals⟩ := Att.moveAt_ok l.move d l.goal h
      exact .inl ⟨d', rfl, by simp [goalsLine, hg, stepOpt, hs, hgoals]⟩
    | error e =>
      obtain ⟨g, hg, hs⟩ := Att.moveAt_error l.move d l.goal h
      exact .inr ⟨_, rfl, by simp [goalsLine, hg, stepOpt, hs]⟩
  | inr c =>
    obtain ⟨hc, hle⟩ := Att.moveAt_inr l.move d l.goal c h
    have hnone : d.goals[l.goal]? = none := List.getElem?_eq_none (hc ▸ hle)
    exact .inr ⟨_, rfl, by simp [goalsLine, hnone]⟩

theorem stepsFrom_done {j : S.Judg} : (ls : Script S) → (n : Nat) → (d : Att S true j) →
    ((Att.stepsFrom n d ls).failed.isNone && (Att.stepsFrom n d ls).att.goals.isEmpty) =
      goalsDone (stepOpt S) d.goals ls
  | [], n, d => by
    cases hg : d.goals <;> simp [Att.stepsFrom, goalsDone, goalsRun, hg]
  | l :: ls, n, d => by
    rcases Att.step_goals d l with ⟨d', hd, hl⟩ | ⟨e, hd, hl⟩
    · have ih := stepsFrom_done ls (n + 1) d'
      simp only [Att.stepsFrom, hd, goalsDone, goalsRun, hl] at ih ⊢
      exact ih
    · simp [Att.stepsFrom, hd, goalsDone, goalsRun, hl]

/-- **What `derives` computes is the run on the list of goals.** -/
theorem derives_eq_goalsDone (j : S.Judg) (ls : Script S) :
    derives S j ls = goalsDone (stepOpt S) [j] ls := by
  show ((run S j ls).failed.isNone && (run S j ls).att.goals.isEmpty) = _
  have e : run S j ls = Att.stepsFrom 0 .goal ls := Att.run_eq_runBySteps .goal ls
  rw [e, stepsFrom_done ls 0 .goal, Att.goals_goal]

end Goals

/-! ## The goals by counts -/

/-- Two answers of a step or of a run: both nothing, or both lists, the
first the counts of the second. -/
def RepO : Option (List CSeq) → Option (List Seq) → Prop
  | none, none => True
  | some js, some ss => CSeq.RepL js ss
  | _, _ => False

theorem CSeq.RepL.append {js js' : List CSeq} {ss ss' : List Seq} (h : CSeq.RepL js ss)
    (h' : CSeq.RepL js' ss') : CSeq.RepL (js ++ js') (ss ++ ss') := by
  induction h with
  | nil => exact h'
  | cons h₁ _ ih => exact .cons h₁ ih

theorem CSeq.RepL.take {js : List CSeq} {ss : List Seq} (h : CSeq.RepL js ss) :
    ∀ k, CSeq.RepL (js.take k) (ss.take k) := by
  induction h with
  | nil => intro k; simpa using CSeq.RepL.nil
  | cons h₁ _ ih =>
    intro k
    cases k with
    | zero => simpa using CSeq.RepL.nil
    | succ k => simpa using CSeq.RepL.cons h₁ (ih k)

theorem CSeq.RepL.drop {js : List CSeq} {ss : List Seq} (h : CSeq.RepL js ss) :
    ∀ k, CSeq.RepL (js.drop k) (ss.drop k) := by
  induction h with
  | nil => intro k; simpa using CSeq.RepL.nil
  | cons h₁ h₂ ih =>
    intro k
    cases k with
    | zero => simpa using CSeq.RepL.cons h₁ h₂
    | succ k => simpa using ih k

theorem CSeq.RepL.get {js : List CSeq} {ss : List Seq} (h : CSeq.RepL js ss) :
    ∀ k : Nat, (js[k]? = none ∧ ss[k]? = none) ∨
      ∃ (j : CSeq) (s : Seq), js[k]? = some j ∧ ss[k]? = some s ∧ CSeq.Rep j s := by
  induction h with
  | nil => intro k; exact .inl ⟨by simp, by simp⟩
  | cons h₁ _ ih =>
    intro k
    cases k with
    | zero => exact .inr ⟨_, _, by simp, by simp, h₁⟩
    | succ k => simpa using ih k

theorem stepOpt_ok {m : Move} {s : Seq} (hok : (m.rule s).ok = true) :
    stepOpt S m s = some (m.rule s).prems := by
  unfold stepOpt
  rw [step_of hok]

theorem stepOpt_error {m : Move} {s : Seq} (hok : ¬ (m.rule s).ok = true) :
    stepOpt S m s = none := by
  have e : S.step m s = .error (m.rule s).why := by
    show step m s = _
    simp [step, hok]
  unfold stepOpt
  rw [e]

/-- One step by counts and one step, at the counts of a sequent. -/
theorem countStep_opt {j : CSeq} {s : Seq} (h : j.Rep s) (m : Move) :
    RepO (countStep m j) (stepOpt S m s) := by
  have hs := countStep_rep h m
  by_cases hok : (m.rule s).ok = true
  · rw [if_pos hok] at hs
    obtain ⟨qs, hq, hrel⟩ := hs
    rw [hq, stepOpt_ok hok]
    exact hrel
  · rw [if_neg hok] at hs
    rw [hs, stepOpt_error hok]
    exact True.intro

theorem goalsLine_rep {js : List CSeq} {ss : List Seq} (h : CSeq.RepL js ss) (l : Line S) :
    RepO (goalsLine (S := S) countStep js l) (goalsLine (stepOpt S) ss l) := by
  rcases h.get l.goal with ⟨h₁, h₂⟩ | ⟨j, s, h₁, h₂, hr⟩
  · simp [goalsLine, h₁, h₂, RepO]
  · have hst := countStep_opt hr l.move
    simp only [goalsLine, h₁, h₂]
    cases hc : countStep l.move j with
    | none =>
      cases ho : stepOpt S l.move s with
      | none => simp [RepO]
      | some ps => rw [hc, ho] at hst; exact hst.elim
    | some qs =>
      cases ho : stepOpt S l.move s with
      | none => rw [hc, ho] at hst; exact hst.elim
      | some ps =>
        rw [hc, ho] at hst
        exact ((h.take l.goal).append hst).append (h.drop (l.goal + 1))

theorem goalsRun_rep : (ls : Script S) → {js : List CSeq} → {ss : List Seq} → CSeq.RepL js ss →
    RepO (goalsRun (S := S) countStep js ls) (goalsRun (stepOpt S) ss ls)
  | [], _, _, h => h
  | l :: ls, js, ss, h => by
    have hl := goalsLine_rep h l
    simp only [goalsRun]
    cases hc : goalsLine (S := S) countStep js l with
    | none =>
      cases ho : goalsLine (stepOpt S) ss l with
      | none => simp [RepO]
      | some ps => rw [hc, ho] at hl; exact hl.elim
    | some qs =>
      cases ho : goalsLine (stepOpt S) ss l with
      | none => rw [hc, ho] at hl; exact hl.elim
      | some ps =>
        rw [hc, ho] at hl
        exact goalsRun_rep ls hl

theorem goalsDone_rep {js : List CSeq} {ss : List Seq} (h : CSeq.RepL js ss) (ls : Script S) :
    goalsDone (S := S) countStep js ls = goalsDone (stepOpt S) ss ls := by
  have hr := goalsRun_rep ls h
  unfold goalsDone
  cases hc : goalsRun (S := S) countStep js ls with
  | none =>
    cases ho : goalsRun (stepOpt S) ss ls with
    | none => rfl
    | some ps => rw [hc, ho] at hr; exact hr.elim
  | some qs =>
    cases ho : goalsRun (stepOpt S) ss ls with
    | none => rw [hc, ho] at hr; exact hr.elim
    | some ps =>
      rw [hc, ho] at hr
      cases hr with
      | nil => rfl
      | cons _ _ => rfl

/-- **The check of a script at a sequent, with the goals by counts.** -/
def Seq.scriptCheck (s : Seq) (ls : Script S) : Bool :=
  goalsDone (S := S) countStep [CSeq.of s] ls

/-- **S29.  The replay of a script by counts is the library's**: the two
checks of a script are one function. -/
theorem scriptCheck_eq (s : Seq) (ls : Script S) : s.scriptCheck ls = derives S s ls := by
  rw [derives_eq_goalsDone]
  exact goalsDone_rep (.cons (.of s) .nil) ls

end GLS

#axioms_within_file [propext, Quot.sound]
