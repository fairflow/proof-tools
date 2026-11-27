# What eight passages of the skill were written to guard against

From the session that drafted the skill in the design phase, 2026-11-27,
in answer to the directing session after the first pruning pass
(`docs/campaigns/pruning-2026-11-27.md`). That pass kept four passages
that no campaign had reached, and did not judge the four checks of
meaning; the question put was what each was written for. The text below
is the design session's, entered as it came. It traced each passage from
its draft's last text against commit `ce28bcc`, and with `git log -S`.

Its second part is input for the test with planted faults.

## (a) Not reached, and kept

1. **Ending a session early** (rule 5). It is the draft's rule 5 turned
   round: "Each stage starts in a fresh session, from a written brief",
   with step 5 of "How a gate is run". That rule guarded two things.
   - Cost. In the one run measured before the draft, a session reading
     its own history again was most of what a stage cost. Rule 5 now
     says "when that cost shows". No cost log has the operator's tokens,
     so it cannot show, and the rule that replaced the draft's has not
     met the measurement that produced the draft's.
   - Whether the documents are enough. A fresh session from a brief is
     the only moment at which the campaign's documents are tested as its
     memory. A session that runs through never tests it.

   The present clause guards a third thing, not the draft's: a campaign
   halted with nobody to open the next session. It covers an end that is
   foreseen. An end without warning leaves no time for a brief, and what
   guards that case is the board being current, which the pass removed
   as not followed. The design session would not put the sentence back:
   the board computed from `statements.md` is the remedy that needs
   nobody to follow it.

2. **A goal off the route ends OPEN.** Not from the draft: it entered at
   `5337dd4` (23 November, from K's notes), and "The operator does not
   set a goal aside" at `1611566`. The draft's counterpart was Q2,
   "becomes a goal, or is set aside with a reason", decided by the
   reviewer at the plan's gate. That guarded against a list of goals
   that contracts to what was proved, so that "every goal PROVED" holds
   by construction. With the gate gone, this clause is the one sentence
   that fixes the list during Prove. "None ended with a goal open" is
   what a strong method and a contracting list would both show. The
   commits can tell them apart: the goals named in the first committed
   file of statements against the closing page's list.

3. **A supervised campaign.** From "How a gate is run". What each gate
   was for:
   - the plan: the choices that cost the campaign to reverse. The only
     gate that changed the work;
   - the rule table and the statements: "A wrong definition compiles,
     passes every bound on axioms and proves its theorems";
   - the test typed by the reviewer: a reader who is not the
     transcriber. In the one run before the draft the reviewer went to
     what was missing and did not work through the exercises, so its
     recorded yield was about use and not about transcription;
   - Run's proposal: R10 of lean-certify. A certifier certifies whatever
     `Holds` says;
   - "A gate is passed when its record says so": an incident. Exercises
     were prepared, the next work began, and nothing recorded that
     anyone typed them.

   Why the six lines stay whatever their count: they are the exception
   to rule 9 and to "Nobody is waited for" in rule 2. Without them the
   text tells the operator to go on past a thing the reviewer has asked
   to pass.

4. **The second shorter path.** From the draft, nearly word for word,
   and abstracted from an instance that exists (the subframe tableau).
   With no source, three of the four checks of meaning have nothing to
   compare with. So the rules, the reading of a judgment and what
   correctness rests on become statements, screened before their
   proofs. The incident behind "before their proofs" is Prove's pitfall
   9, a model construction that carried as an invariant the lemma its
   proof was to establish.

## (b) The four checks of meaning

1. **The tools.** From the draft, taken over from the earlier adoption
   skill. `#rules` exists so that the comparison is of two figures and
   not of a figure with Lean source, where implicit arguments and the
   order of hypotheses hide a difference. `#slime` is about form:
   whether the family can be taken apart by cases. No fault of meaning
   shows in it.
2. **The source's derivations.** In the draft this was the test, and its
   point was the person. Run by the operator from a script it is a
   different check, a mechanical replay.
3. **The cold reader.** Not from the draft (`1611566`). It stands where
   the draft had the reviewer read the rule table and the statements.
4. **Soundness and completeness first.** In the draft "Soundness before
   completeness", from the incident in Survey's pitfall 2: completeness
   proved while soundness was false, at two versions of one side
   condition. The draft meant an order of work. Calling it a check of
   the transcription is from `1611566`. The pruning pass found the order
   not kept in MALL and DILL.

## For the test with planted faults

1. **Direction.** A rule made too permissive (a side condition dropped,
   a premise weakened) cannot be caught by check 2: every derivation of
   the source still replays. A rule made too restrictive is caught by
   check 2 only where an example uses the instance. Three of the
   collation's four faults are permissive or neutral, and none makes a
   rule of the family stricter. The table needs both directions, or
   checks 2 and 4 will each look blind on half of it.
2. **The known non-theorems** were the draft's guard in the permissive
   direction where there is no semantics (the plan's section, and item
   3 of the tests in `reference/explore.md` §10). They are not among the
   four checks in the main file. Run them as a fifth row.
3. Give `#slime` a row apart from `#rules`, and expect it empty. The
   `#rules` row measures the reader who compares, since the command only
   prints. It prints the names of the functions a rule uses and not what
   they compute, so plant one fault in an auxiliary definition (an
   operation on contexts, a substitution).
4. A fault that leaves the derivable judgments unchanged (a structural
   rule built in, an admissible variant) passes check 4 by
   construction. Plant one, to see whether the two comparisons catch it.
5. A fault in the semantics or in `Valid`: both theorems are then proved
   against the wrong thing, and only the reading back can catch it.
6. **The shared misreading.** At a place where a source is ambiguous or
   misprinted (the campaigns found several), put the plausible wrong
   reading in the family and see whether the second transcription makes
   the same choice. A cold reader is the same kind of reader as the
   operator; the reviewer was not.
7. Whoever compares must not know which copy is faulty, or that any is.
   Include copies with no fault, and one with a harmless difference
   (premises in another order), so that false alarms are counted.
8. "A rule missing from `step` only" is caught by S2 with certainty,
   since its proof fails. That is a theorem and no check of meaning; it
   is a control row.

What the design session does not know: the faulty tables of the two
incidents in Survey's pitfalls (it has their text only, from the earlier
skill), and what K's note behind `5337dd4` had in view.
