/-
# `ProofTools.Explore`: a proof system, its attempts, scripts and checkers

The parts, in the order they build on one another:

| file | what |
|---|---|
| `System` | `ProofSystem`; attempts `Att`, derivations `Der`; soundness of an attempt |
| `Zipper` | the zipper of attempts, an instance of `ProofTools.Zipper` |
| `Script` | scripts; one move from the root, the specification of a step |
| `Cursor` | `run`, with a zipper kept from line to line |
| `Run` | `run` is the run by steps; a script read back rebuilds its attempt |
| `Certify` | `derives`, `certifier`, `Evaluator`, `engine`: the two checkers |
| `Tac` | scripts as programs: `Script.shift` and the combinators on tactics |
| `Tactic` | `Explorable`; the tactics `apply_move`, `apply_script`, `leave_open` |
| `Motion` | the motions of the cursor (`up`, `down i`, `left`, `right`, `top`, `goal k`), their laws, and the motions that can be made from a position |
| `Walk` | the view at a position; the command `#walk`, to look at an attempt that is built, by typing motions or by clicking the ones it offers |
| `Panel` | a trial: the attempt drawn as a tree in the infoview, with nodes to click (`set_option walk.panel true`) |
-/
import ProofTools.Explore.Certify
import ProofTools.Explore.Tac
import ProofTools.Explore.Tactic
import ProofTools.Explore.Motion
import ProofTools.Explore.Panel
import ProofTools.Explore.Walk
