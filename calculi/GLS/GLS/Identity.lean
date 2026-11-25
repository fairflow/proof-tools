/-
The identity on every formula (the source's `Id_all_form`, l. 331 of the
Coq file): by recursion on the formula, as there.  A function on
derivations, written by matching.  Theory file: it ends with its bound on
axioms.
-/
import GLS.Lemmas

namespace GLS

/-- **The identity on every formula**: a sequent with a formula on both
sides is derivable in GLS. -/
def Fam.id : Identity
  | .var p, _, _, hΓ, hΔ => .idP p hΓ hΔ
  | ⊥, _, _, hΓ, _ => .botL hΓ
  | A ⟶ B, _, _, hΓ, hΔ =>
      .impR A B hΔ
        (.impL A B (List.mem_cons_of_mem _ hΓ)
          (Fam.id A (mem_erase_of_ne (Form.ne_imp_left A B) (List.mem_cons_self ..))
            (List.mem_cons_self ..))
          (Fam.id B (List.mem_cons_self ..) (List.mem_cons_self ..)))
  | □A, _, _, hΓ, hΔ =>
      .glr A hΔ (Fam.id A (List.mem_append_left _ (body_mem_xbox hΓ)) (List.mem_singleton.2 rfl))

end GLS

#axioms_within_file [propext, Quot.sound]
