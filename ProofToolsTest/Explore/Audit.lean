/-
The axioms of `ProofTools.Explore`, as upper bounds (`#axioms_within`: a
declaration may use fewer axioms than its list allows, and none outside
it).  Each theory file of the library also carries its own bound, at its
end (`#axioms_within_file`).

What is trusted when a script is accepted is `derives`, `Att.sound` and the
instance's soundness theorem.  That path is within `[propext, Quot.sound]`:
`Classical.choice` is used only in the theorems that compare `run` with its
specification, where `omega` brings it.
-/
import ProofTools.Audit
import ProofTools.Explore
import ProofToolsTest.Explore.Calculus

open ProofTools ProofTools.Explore

/-! ## The path of trust: no `Classical.choice` -/

#axioms_within Att.sound [propext, Quot.sound]
#axioms_within Der.sound [propext, Quot.sound]
#axioms_within derives_sound [propext, Quot.sound]
#axioms_within certifier [propext, Quot.sound]
#axioms_within Evaluator.certifier [propext, Quot.sound]
#axioms_within engine [propext, Quot.sound]
#axioms_within Der.ofScript [propext, Quot.sound]

/-! ## The functions that run: no `Classical.choice` -/

#axioms_within run [propext, Quot.sound]
#axioms_within Att.runBySteps [propext, Quot.sound]
#axioms_within Att.script [propext, Quot.sound]
#axioms_within derives [propext, Quot.sound]
#axioms_within Tac.andThen [propext, Quot.sound]
#axioms_within Tac.iterate [propext, Quot.sound]

/-! ## What a step does, and the zipper's laws -/

#axioms_within Att.moveAt_of_le [propext, Quot.sound]
#axioms_within Att.moveAt_inr [propext, Quot.sound]
#axioms_within Att.moveAt_ok [propext, Quot.sound]
#axioms_within Att.moveAt_error [propext, Quot.sound]
#axioms_within Path.goals_plug [propext, Quot.sound]
#axioms_within Crumb.unplug_plug [propext, Quot.sound]
#axioms_within Path.canon [propext, Quot.sound]
#axioms_within Zip.Deriv.Zipper.descend_addr [propext, Quot.sound]

/-! ## `run` and its specification -/

#axioms_within Cursor.seek_some [propext, Classical.choice, Quot.sound]
#axioms_within Cursor.seek_none [propext, Classical.choice, Quot.sound]
#axioms_within Path.moveAt_plug [propext, Quot.sound]
#axioms_within Att.run_eq_runBySteps [propext, Classical.choice, Quot.sound]
#axioms_within run_script [propext, Classical.choice, Quot.sound]
#axioms_within run_script_att [propext, Classical.choice, Quot.sound]
#axioms_within Att.runFrom_append [propext, Classical.choice, Quot.sound]
#axioms_within derives_script [propext, Classical.choice, Quot.sound]

/-! ## Scripts as programs -/

#axioms_within Att.runFrom_shift [propext, Classical.choice, Quot.sound]
#axioms_within Tac.valid_move [propext, Classical.choice, Quot.sound]
#axioms_within Tac.valid_orElse [propext, Quot.sound]
#axioms_within Tac.valid_andThen [propext, Classical.choice, Quot.sound]
#axioms_within Tac.valid_iterate [propext, Classical.choice, Quot.sound]

/-! ## The example calculus -/

#axioms_within ProofToolsTest.Explore.sound [propext, Quot.sound]
#axioms_within ProofToolsTest.Explore.evaluator [propext, Quot.sound]
#axioms_within ProofToolsTest.Explore.ipcEngine [propext, Quot.sound]
#axioms_within ProofToolsTest.Explore.auto_valid [propext, Classical.choice, Quot.sound]
