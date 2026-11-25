/-
The facts of the corpus, each with its certificate.  Written by `glsrun
facts` (`Main.lean`); do not edit.  The kernel checks every certificate
when this file is elaborated: a tree of moves for a derivation in GLS, a
finite tree against derivability.
-/
import GLS.Corpus.Basic

namespace GLS.Corpus.Facts

open GLS GLS.Corpus

def axK : Fam ([] ⇒ [□(p ⟶ q) ⟶ □p ⟶ □q]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.impR
    (GLS.Form.box (GLS.Form.imp (GLS.Form.var 0) (GLS.Form.var 1)))
    (GLS.Form.imp (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.box (GLS.Form.var 1))))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.impR (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.box (GLS.Form.var 1)))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.glr (GLS.Form.var 1))
          [((),
            ProofTools.Zip.RTree.node
              (GLS.Move.impL (GLS.Form.var 0) (GLS.Form.var 1))
              [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) []),
               ((), ProofTools.Zip.RTree.node (GLS.Move.idP 1) [])])])])])

def ax4 : Fam ([] ⇒ [□p ⟶ □□p]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.impR (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.box (GLS.Form.box (GLS.Form.var 0))))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.glr (GLS.Form.box (GLS.Form.var 0)))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.glr (GLS.Form.var 0))
          [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])])])])

def axLob : Fam ([] ⇒ [□(□p ⟶ p) ⟶ □p]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.impR
    (GLS.Form.box (GLS.Form.imp (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0)))
    (GLS.Form.box (GLS.Form.var 0)))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.glr (GLS.Form.var 0))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.impL (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0))
          [((),
            ProofTools.Zip.RTree.node
              (GLS.Move.glr (GLS.Form.var 0))
              [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])]),
           ((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])])])])

def idBoxImp : Fam ([□(p ⟶ q)] ⇒ [□(p ⟶ q)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.glr (GLS.Form.imp (GLS.Form.var 0) (GLS.Form.var 1)))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.impR (GLS.Form.var 0) (GLS.Form.var 1))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.impL (GLS.Form.var 0) (GLS.Form.var 1))
          [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) []),
           ((), ProofTools.Zip.RTree.node (GLS.Move.idP 1) [])])])])

def exFalsoBox : Fam ([] ⇒ [□⊥ ⟶ □p]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.impR (GLS.Form.box (GLS.Form.bot)) (GLS.Form.box (GLS.Form.var 0)))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.glr (GLS.Form.var 0))
      [((), ProofTools.Zip.RTree.node (GLS.Move.botL) [])])])

def godel2 : Fam ([] ⇒ [□(□⊥ ⟶ ⊥) ⟶ □⊥]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.impR
    (GLS.Form.box (GLS.Form.imp (GLS.Form.box (GLS.Form.bot)) (GLS.Form.bot)))
    (GLS.Form.box (GLS.Form.bot)))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.glr (GLS.Form.bot))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.impL (GLS.Form.box (GLS.Form.bot)) (GLS.Form.bot))
          [((),
            ProofTools.Zip.RTree.node
              (GLS.Move.glr (GLS.Form.bot))
              [((), ProofTools.Zip.RTree.node (GLS.Move.botL) [])]),
           ((), ProofTools.Zip.RTree.node (GLS.Move.botL) [])])])])

def boxLobBody : Fam ([] ⇒ [□p ⟶ □(□p ⟶ p)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.impR
    (GLS.Form.box (GLS.Form.var 0))
    (GLS.Form.box (GLS.Form.imp (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0))))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.glr (GLS.Form.imp (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0)))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.impR (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0))
          [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])])])])

def lobRuleShape : Fam ([□(□p ⟶ p)] ⇒ [□□p, □p]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (GLS.Move.glr (GLS.Form.box (GLS.Form.var 0)))
  [((),
    ProofTools.Zip.RTree.node
      (GLS.Move.impL (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0))
      [((),
        ProofTools.Zip.RTree.node
          (GLS.Move.glr (GLS.Form.var 0))
          [((),
            ProofTools.Zip.RTree.node
              (GLS.Move.impL (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0))
              [((),
                ProofTools.Zip.RTree.node
                  (GLS.Move.glr (GLS.Form.var 0))
                  [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])]),
               ((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])])]),
       ((),
        ProofTools.Zip.RTree.node
          (GLS.Move.glr (GLS.Form.var 0))
          [((),
            ProofTools.Zip.RTree.node
              (GLS.Move.impL (GLS.Form.box (GLS.Form.var 0)) (GLS.Form.var 0))
              [((),
                ProofTools.Zip.RTree.node
                  (GLS.Move.glr (GLS.Form.var 0))
                  [((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])]),
               ((), ProofTools.Zip.RTree.node (GLS.Move.idP 0) [])])])])])

theorem notT : ¬ Derivable ([] ⇒ [□p ⟶ p]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [])

theorem notAtom : ¬ Derivable ([] ⇒ [p]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [])

theorem notConsistency : ¬ Derivable ([] ⇒ [□⊥ ⟶ ⊥]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [])

theorem notBoxT : ¬ Derivable ([] ⇒ [□(□p ⟶ p)]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [GLS.Tree.node [] []])

theorem notConverseK : ¬ Derivable ([] ⇒ [(□p ⟶ □q) ⟶ □(p ⟶ q)]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [GLS.Tree.node [] [], GLS.Tree.node [0] []])

theorem notConverse4 : ¬ Derivable ([] ⇒ [□□p ⟶ □p]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [GLS.Tree.node [] []])

theorem notLobBody : ¬ Derivable ([] ⇒ [(□p ⟶ p) ⟶ p]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [GLS.Tree.node [] []])

theorem notLinear : ¬ Derivable ([] ⇒ [□(□p ⟶ q), □(□q ⟶ p)]) :=
  noDerivable.verdict _ (GLS.Tree.node [] [GLS.Tree.node [] [], GLS.Tree.node [] []])

end GLS.Corpus.Facts

#axioms_within_file [propext, Quot.sound]
