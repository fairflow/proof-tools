/-
The facts of the corpus.  Written by `mallrun facts` (`Main.lean`); do not
edit.  The kernel checks each when this file is elaborated: for a
derivation, the tree of moves that the search by lazy splitting found;
against one, a finite phase structure on a cyclic group that refutes the
sequent, where the producer of `MALL/ModelRun.lean` has one, and otherwise
a saturated set of sequents of which it is a member (`MALL/SatRun.lean`),
from the producer of `MALL/Refute.lean`.
-/
import MALL.Corpus.Basic
import MALL.ModelRun
import MALL.SatRun

namespace MALL.Corpus.Facts

open MALL MALL.Corpus

def axLetter : Fam [p, pᗮ] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) [])

def one : Fam [𝟏] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node (MALL.Move.one) [])

def p26 : Fam [pᗮ, p ⊕ q] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.plus₁ (MALL.Form.atom 0) (MALL.Form.atom 1))
  [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) [])])

def p5with : Fam [pᗮ ⅋ (p & p)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.wth (MALL.Form.atom 0) (MALL.Form.atom 0)))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.wth (MALL.Form.atom 0) (MALL.Form.atom 0))
      [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
       ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) [])])])

def idTensor : Fam [pᗮ ⅋ qᗮ, p ⊗ q] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1))) [])

def tensorComm : Fam [pᗮ ⅋ qᗮ, q ⊗ p] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.natom 1))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.tensor (MALL.Form.atom 1) (MALL.Form.atom 0) [MALL.Form.natom 1])
      [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 1)) []),
       ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) [])])])

def tensorAssoc : Fam [(pᗮ ⅋ qᗮ) ⅋ rᗮ, p ⊗ (q ⊗ r)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1)) (MALL.Form.natom 2))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.natom 1))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor
            (MALL.Form.atom 0)
            (MALL.Form.tensor (MALL.Form.atom 1) (MALL.Form.atom 2))
            [MALL.Form.natom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.tensor (MALL.Form.atom 1) (MALL.Form.atom 2) [MALL.Form.natom 1])
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 1)) []),
               ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 2)) [])])])])])

def tensorUnit : Fam [⊥ ⅋ pᗮ, p] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.bot) (MALL.Form.natom 0))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.bot)
      [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) [])])])

def tensorUnit' : Fam [pᗮ, 𝟏 ⊗ p] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.tensor (MALL.Form.one) (MALL.Form.atom 0) [])
  [((), ProofTools.Zip.RTree.node (MALL.Move.one) []),
   ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) [])])

def parUnit : Fam [𝟏 ⊗ pᗮ, p] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.tensor (MALL.Form.one) (MALL.Form.natom 0) [])
  [((), ProofTools.Zip.RTree.node (MALL.Move.one) []),
   ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) [])])

def withProj : Fam [pᗮ ⊕ qᗮ, p] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.plus₁ (MALL.Form.natom 0) (MALL.Form.natom 1))
  [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) [])])

def plusInj : Fam [pᗮ, p ⊕ q] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.plus₁ (MALL.Form.atom 0) (MALL.Form.atom 1))
  [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) [])])

def withUnit : Fam [𝟎 ⊕ pᗮ, p] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.plus₂ (MALL.Form.zero) (MALL.Form.natom 0))
  [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) [])])

def distrib : Fam [pᗮ ⅋ (qᗮ & rᗮ), (p ⊗ q) ⊕ (p ⊗ r)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.wth (MALL.Form.natom 1) (MALL.Form.natom 2)))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.wth (MALL.Form.natom 1) (MALL.Form.natom 2))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.plus₁
            (MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.atom 1))
            (MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.atom 2)))
          [((),
            ProofTools.Zip.RTree.node
              (MALL.Move.tensor (MALL.Form.atom 0) (MALL.Form.atom 1) [MALL.Form.natom 0])
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
               ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 1)) [])])]),
       ((),
        ProofTools.Zip.RTree.node
          (MALL.Move.plus₂
            (MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.atom 1))
            (MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.atom 2)))
          [((),
            ProofTools.Zip.RTree.node
              (MALL.Move.tensor (MALL.Form.atom 0) (MALL.Form.atom 2) [MALL.Form.natom 0])
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
               ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 2)) [])])])])])

def distrib' : Fam [(pᗮ ⅋ qᗮ) & (pᗮ ⅋ rᗮ), p ⊗ (q ⊕ r)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.wth
    (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1))
    (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 2)))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.natom 1))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor
            (MALL.Form.atom 0)
            (MALL.Form.plus (MALL.Form.atom 1) (MALL.Form.atom 2))
            [MALL.Form.natom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.plus₁ (MALL.Form.atom 1) (MALL.Form.atom 2))
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 1)) [])])])]),
   ((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.natom 2))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor
            (MALL.Form.atom 0)
            (MALL.Form.plus (MALL.Form.atom 1) (MALL.Form.atom 2))
            [MALL.Form.natom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.plus₂ (MALL.Form.atom 1) (MALL.Form.atom 2))
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 2)) [])])])])])

def parDistrib : Fam [pᗮ ⊗ (qᗮ ⊕ rᗮ), (p ⅋ q) & (p ⅋ r)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.wth
    (MALL.Form.par (MALL.Form.atom 0) (MALL.Form.atom 1))
    (MALL.Form.par (MALL.Form.atom 0) (MALL.Form.atom 2)))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.atom 0) (MALL.Form.atom 1))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor
            (MALL.Form.natom 0)
            (MALL.Form.plus (MALL.Form.natom 1) (MALL.Form.natom 2))
            [MALL.Form.atom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.plus₁ (MALL.Form.natom 1) (MALL.Form.natom 2))
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 1)) [])])])]),
   ((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.atom 0) (MALL.Form.atom 2))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor
            (MALL.Form.natom 0)
            (MALL.Form.plus (MALL.Form.natom 1) (MALL.Form.natom 2))
            [MALL.Form.atom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.plus₂ (MALL.Form.natom 1) (MALL.Form.natom 2))
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 2)) [])])])])])

def zeroAbsorbs : Fam [⊤ ⅋ pᗮ, 𝟎] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.top) (MALL.Form.natom 0))
  [((), ProofTools.Zip.RTree.node (MALL.Move.top) [])])

def topAbsorbs : Fam [𝟎 ⊗ pᗮ, ⊤] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node (MALL.Move.top) [])

def halfDistrib : Fam [pᗮ ⅋ (qᗮ ⊕ rᗮ), (p ⊗ q) & (p ⊗ r)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.par (MALL.Form.natom 0) (MALL.Form.plus (MALL.Form.natom 1) (MALL.Form.natom 2)))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.wth
        (MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.atom 1))
        (MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.atom 2)))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor (MALL.Form.atom 0) (MALL.Form.atom 1) [MALL.Form.natom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.plus₁ (MALL.Form.natom 1) (MALL.Form.natom 2))
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 1)) [])])]),
       ((),
        ProofTools.Zip.RTree.node
          (MALL.Move.tensor (MALL.Form.atom 0) (MALL.Form.atom 2) [MALL.Form.natom 0])
          [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
           ((),
            ProofTools.Zip.RTree.node
              (MALL.Move.plus₂ (MALL.Form.natom 1) (MALL.Form.natom 2))
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 2)) [])])])])])

def halfDistribPar : Fam [(pᗮ ⊗ qᗮ) & (pᗮ ⊗ rᗮ), p ⅋ (q ⊕ r)] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.wth
    (MALL.Form.tensor (MALL.Form.natom 0) (MALL.Form.natom 1))
    (MALL.Form.tensor (MALL.Form.natom 0) (MALL.Form.natom 2)))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.atom 0) (MALL.Form.plus (MALL.Form.atom 1) (MALL.Form.atom 2)))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.plus₁ (MALL.Form.atom 1) (MALL.Form.atom 2))
          [((),
            ProofTools.Zip.RTree.node
              (MALL.Move.tensor (MALL.Form.natom 0) (MALL.Form.natom 1) [MALL.Form.atom 0])
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) []),
               ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 1)) [])])])]),
   ((),
    ProofTools.Zip.RTree.node
      (MALL.Move.par (MALL.Form.atom 0) (MALL.Form.plus (MALL.Form.atom 1) (MALL.Form.atom 2)))
      [((),
        ProofTools.Zip.RTree.node
          (MALL.Move.plus₂ (MALL.Form.atom 1) (MALL.Form.atom 2))
          [((),
            ProofTools.Zip.RTree.node
              (MALL.Move.tensor (MALL.Form.natom 0) (MALL.Form.natom 2) [MALL.Form.atom 0])
              [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) []),
               ((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 2)) [])])])])])

def plusTwice : Fam [p ⊕ pᗮ, p ⊕ pᗮ] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.plus₁ (MALL.Form.atom 0) (MALL.Form.natom 0))
  [((),
    ProofTools.Zip.RTree.node
      (MALL.Move.plus₂ (MALL.Form.atom 0) (MALL.Form.natom 0))
      [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.natom 0)) [])])])

def topSplit : Fam [p, q, ⊤ ⊗ ⊤] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.tensor (MALL.Form.top) (MALL.Form.top) [MALL.Form.atom 1, MALL.Form.atom 0])
  [((), ProofTools.Zip.RTree.node (MALL.Move.top) []),
   ((), ProofTools.Zip.RTree.node (MALL.Move.top) [])])

def topSlack : Fam [p ⊗ ⊤, pᗮ, q, r] :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (MALL.Move.tensor (MALL.Form.atom 0) (MALL.Form.top) [MALL.Form.natom 0])
  [((), ProofTools.Zip.RTree.node (MALL.Move.ax (MALL.Form.atom 0)) []),
   ((), ProofTools.Zip.RTree.node (MALL.Move.top) [])])

theorem weakening : ¬ Derivable [𝟏, 𝟏] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [false, true], val := [[false, false]] })

theorem weakening' : ¬ Derivable [𝟏, p, pᗮ] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [false, true], val := [[true, false]] })

theorem affine : ¬ Derivable [pᗮ ⅋ 𝟏] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [true, false], val := [[false, true]] })

theorem contraction : ¬ Derivable [p ⊕ pᗮ] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [true, false], val := [[false, true]] })

theorem p5tensor : ¬ Derivable [pᗮ ⅋ (p ⊗ p)] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [true, false], val := [[false, true]] })

theorem empty : ¬ Derivable [] :=
  noDerivableBy.verdict _ ({ k := 0, bot := [false], val := [[false]] })

theorem zero : ¬ Derivable [𝟎] :=
  noDerivableBy.verdict _ ({ k := 0, bot := [false], val := [[false]] })

theorem zeroCtx : ¬ Derivable [𝟎, p] :=
  noDerivableBy.verdict _ ({ k := 0, bot := [false], val := [[false]] })

theorem bot : ¬ Derivable [⊥] :=
  noDerivableBy.verdict _ ({ k := 0, bot := [false], val := [[false]] })

theorem letter : ¬ Derivable [p] :=
  noDerivableBy.verdict _ ({ k := 0, bot := [false], val := [[false]] })

theorem tensorDual : ¬ Derivable [p ⊗ pᗮ] :=
  noDerivableBy.verdict _ ({ k := 0, bot := [false], val := [[false]] })

theorem mix : ¬ Derivable [p ⅋ pᗮ, q ⅋ qᗮ] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [false, true], val := [[true, false], [true, false]] })

theorem halfDistribConv : ¬ Derivable [(pᗮ ⅋ qᗮ) ⊕ (pᗮ ⅋ rᗮ), p ⊗ (q & r)] :=
  noDerivableBySet.verdict _ ([[MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2)), MALL.Form.plus (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1)) (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 2))], [MALL.Form.atom 0, MALL.Form.plus (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1)) (MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 2))], [MALL.Form.atom 0, MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 2)], [MALL.Form.atom 0, MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1)], [MALL.Form.atom 0, MALL.Form.natom 0, MALL.Form.natom 2], [MALL.Form.natom 0, MALL.Form.natom 1, MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2))], [MALL.Form.atom 0, MALL.Form.natom 2], [MALL.Form.atom 2, MALL.Form.natom 1], [MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2)), MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 2)], [MALL.Form.atom 0], [MALL.Form.atom 0, MALL.Form.natom 1], [MALL.Form.atom 0, MALL.Form.natom 0, MALL.Form.natom 1], [MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2)), MALL.Form.par (MALL.Form.natom 0) (MALL.Form.natom 1)], [MALL.Form.natom 2, MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2)], [MALL.Form.atom 1, MALL.Form.natom 2], [MALL.Form.natom 0, MALL.Form.natom 2, MALL.Form.tensor (MALL.Form.atom 0) (MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2))], [MALL.Form.natom 1, MALL.Form.wth (MALL.Form.atom 1) (MALL.Form.atom 2)]])

theorem withTensor : ¬ Derivable [pᗮ ⊕ qᗮ, p ⊗ q] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [true, false], val := [[false, true], [false, true]] })

theorem tensorWith : ¬ Derivable [pᗮ ⅋ qᗮ, p & q] :=
  noDerivableBy.verdict _ ({ k := 1, bot := [true, false], val := [[false, true], [true, false]] })

end MALL.Corpus.Facts

#axioms_within_file [propext, Quot.sound]
