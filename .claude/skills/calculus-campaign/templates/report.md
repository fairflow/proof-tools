# <CALCULUS>, stage <stage number> (<its name>): report

*Template, kept as `report-<stage number>-<date>.md`. Keep the five parts
and their order. Write what is so; where something was not checked, say
"not checked". A gate note in the middle of a stage has the same parts,
as short as they can be. The Survey's report goes with the plan: its
part (ii) is the plan's Q2.*

Written <date and time, from the clock>, for <the reviewer>. Stage begun
on the word of <date>: "<the words>".

## (i) What was done

Branch `<…>`, commit `<…>`.

1. <Each thing made, one line, with its file.>

What it cost: <the rows of `cost-log.md` for this stage, or their totals>.

## (ii) The statements

**PROVED**, checked by the kernel, no `sorry`, within <the bound>:

    <statement>                                                  (<name>)

**OPEN**: <each; whether attempted; what tests show about it, and on how
many cases. A statement that only tests support is OPEN>.

**REFUTED**: <each, with its countermodel; or "nothing">.

**The goals** (in the report of Prove, and in the closing report): <each
goal of the plan, those from the standing list first: PROVED or OPEN>.

## (iii) What to look at, and what to try

The file: `<…>`. To build: `<command, naming its folder>`.

What should happen, item by item:

* <an exercise or a command>: <what the reviewer should see>.

Measurements, with the machine and the date: <timings; sizes; kernel time
against certificate size>.

## (iv) What differed

1. **From the plan**: <…>
2. **From the source**: <each divergence added to the log at this stage>.
3. **From the skill**: <from `method-notes.md`: every place it was wrong,
   silent or unclear, and what was done there>.
4. **Asked of the library**: <any change `proof-tools` would have needed;
   none was made>.

## (v) For you to decide

1. <The gate of this stage: pass, or what to change. At the Survey's
   gate: which results are goals, beyond those that are goals by rule.>
2. <Each open choice, with a recommendation.>

---

*In the closing report (after stage 4) part (iv) ends with the
retrospective: what the campaign adopted, proved and runs; what is OPEN;
and the changes to make to the skill and its templates, each with the
place in the text.*
