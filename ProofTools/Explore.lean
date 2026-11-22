/-
# `ProofTools.Explore`: a proof system, its attempts, scripts and checkers

The parts, in the order they build on one another:

| file | what |
|---|---|
| `System` | `ProofSystem`; attempts `Att`, derivations `Der`; soundness of the moves for a family into any sort (`SoundT`, and `Sound` for a proposition); the map out (`Att.mapOut`, `Der.mapOut`) |
| `Zipper` | the zipper of attempts, an instance of `ProofTools.Zipper` |
| `Script` | scripts; one move from the root, the specification of a step |
| `Cursor` | `run`, with a zipper kept from line to line |
| `Run` | `run` is the run by steps; a script read back rebuilds its attempt |
| `Cert` | a tree of moves as a certificate, a rose tree of `ProofTools.Zipper.Rose`: `Cert.check`, `Der.ofCert`, `Att.cert`, and that derivations and trees that check are the same things |
| `Certify` | `derives`; the certifiers `certifier` (of scripts) and `Cert.certifier` (of trees of moves), their property a proposition or a type; `engine` |
| `Tac` | scripts as programs: `Script.shift` and the combinators on tactics |
| `Motion` | the motions of the cursor (`up`, `down i`, `left`, `right`, `top`, `goal k`), their laws, the one loop over motions (`Cursor.trail`), and the motions that can be made from a position |
| `View` | `Explorable`; an attempt drawn as text: all of it (`Att.render`), the view at a position (`Cursor.view`), the view with every branch drawn (`Cursor.viewAll`) |
| `Tactic` | the tactics `apply_move`, `apply_script`, `leave_open`; the query `apply_move where`, which draws the attempt so far; a goal shown as its judgment |
| `Walk` | to look at an attempt that is built: the command `#walk`, by typing motions or by clicking the ones it offers; the goal `Walk d`, by a tactic block whose lines are motions |
| `Panel` | a trial: the attempt drawn as a tree in the infoview, with nodes to click (`set_option walk.panel true`) |
-/
import ProofTools.Explore.Certify
import ProofTools.Explore.Tac
import ProofTools.Explore.Motion
import ProofTools.Explore.View
import ProofTools.Explore.Tactic
import ProofTools.Explore.Panel
import ProofTools.Explore.Walk
