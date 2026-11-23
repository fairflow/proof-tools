/-
Tests of the trees of moves of `ProofTools.Explore.Cert` on the example
calculus (`ProofToolsTest/Explore/Calculus.lean`): a tree checked by
compiled code and by the kernel; the tree of a derivation, and the
derivation of a tree; trees compared, printed and drawn by what the library
has for rose trees; wrong trees rejected; the certifier of trees at a
proposition and at a type; an attempt with open goals as a function on
trees; the tree of a derivation where a node's equation is decided; the
tree and the script of one derivation, each from the other.  The cost of
the two checks in the kernel is in `CertScale.lean`.
-/
import ProofToolsTest.Explore.Calculus
import ProofToolsTest.Explore.MapOut

namespace ProofToolsTest.Explore.CertTest

open ProofTools ProofTools.Explore ProofToolsTest.Explore ProofToolsTest.Explore.MapOutTest

/-- `⊢ (p ∧ q) → (q ∧ p)`. -/
abbrev swapSeq : Seq := [] ⊢ (p ⋏ q) ⟶ (q ⋏ p)

/-- Its tree of moves, written by hand. -/
def swapCert : Cert IPC :=
  .mk .impR [.mk (.andL p q) [.mk .andR [.mk .ax [], .mk .ax []]]]

/-! ## A tree, checked -/

#guard Cert.check swapSeq swapCert

-- in the kernel
example : Cert.check swapSeq swapCert = true := by decide +kernel

/-! ## The tree of a derivation, and the derivation of a tree -/

-- the tree of the derivation the tactic built: the kernel evaluates `Att.cert`
example : swap.cert = swapCert := rfl

-- a tree is a rose tree, with nothing on its edges
example : swapCert =
    .node .impR [((), .node (.andL p q) [((), .node .andR [((), .node .ax []), ((), .node .ax [])])])] :=
  rfl

-- PROVED for every derivation (`Att.check_cert`): its tree checks
example : Cert.check swapSeq swap.cert = true := Att.check_cert swap

/-- The derivation of the tree. -/
def swapOfCert : Der IPC swapSeq := Der.ofCert swapSeq swapCert (by decide +kernel)

-- it is the derivation the tactic built: the kernel evaluates `Der.ofCert`
example : swapOfCert = swap := rfl

-- PROVED for every tree that checks, and for every derivation: the two round trips
example (h : Cert.check swapSeq swapCert = true) : (Der.ofCert swapSeq swapCert h).cert = swapCert :=
  Att.cert_ofCert swapCert swapSeq h
example (h : Cert.check swapSeq swap.cert = true) : Der.ofCert swapSeq swap.cert h = swap :=
  Der.ofCert_cert swap h

-- a derivation is determined by its tree
example (d : Der IPC swapSeq) (h : d.cert = swapCert) : d = swap := Att.cert_inj h

-- two premises with one judgment keep their own trees
example : twice.cert = .mk .andR [.mk .ax [], .mk (.impL p p) [.mk .ax [], .mk .ax []]] := rfl

/-! ## Compared, printed and drawn: the library's rose trees -/

-- `RTree.beq`, proved lawful in `ProofTools.Zipper.RoseRender`
#guard swap.cert == swapCert
#guard twice.cert != swapCert
example : (swap.cert == swapCert) = true := by decide +kernel

/--
info: ProofTools.Zip.RTree.node
  (ProofToolsTest.Explore.Move.andR)
  [((), ProofTools.Zip.RTree.node (ProofToolsTest.Explore.Move.ax) []),
   ((), ProofTools.Zip.RTree.node (ProofToolsTest.Explore.Move.ax) [])]
-/
#guard_msgs in
#eval (Cert.mk .andR [.mk .ax [], .mk .ax []] : Cert IPC)

/--
info: impR
     ↦ andL p0 p1
         ↦ andR
             ↦ ax
             ↦ ax
-/
#guard_msgs in
#eval IO.println (swap.cert.drawWith (fun _ => "") Move.show)

-- Huet's zipper on a tree of moves: down twice, and the move there
#guard ((Zip.Zipper.ofTree swapCert).downAt 0 |>.bind (·.downAt 0) |>.map (·.label)) == some Move.andR

/-! ## Wrong trees are rejected -/

-- a move that does not apply
example : Cert.check (S := IPC) swapSeq (.mk .andR []) = false := by decide +kernel
-- a premise with no tree
example : Cert.check (S := IPC) swapSeq (.mk .impR [.mk (.andL p q) [.mk .andR [.mk .ax []]]]) = false := by
  decide +kernel
-- a tree with no premise
example : Cert.check (S := IPC) swapSeq
    (.mk .impR [.mk (.andL p q) [.mk .andR [.mk .ax [], .mk .ax [], .mk .ax []]]]) = false := by
  decide +kernel

-- as a `verdict` term a wrong tree does not elaborate: the gate, watched failing
example : True := by
  fail_if_success
    have : Valid swapSeq :=
      (Cert.certifier sound.soundT).verdict swapSeq (Cert.mk (S := IPC) .impR [.mk .ax []])
  trivial

/-! ## The certifier of trees, at a proposition and at a type -/

-- the kernel checks the tree
example : Valid swapSeq := (Cert.certifier sound.soundT).verdict swapSeq swapCert

/-- A tree certifies a derivation of the calculus, as data: the kernel
checks the tree, and the certifier's `sound` builds the derivation. -/
def swapByTree : G3 swapSeq := (Cert.certifier soundT).verdict swapSeq swapCert

#guard swapByTree.rules == swapG3.rules
example : swapByTree.rules = ["impR", "andL", "andR", "ax", "ax"] := by decide +kernel
example : swapByTree = swapG3 := rfl

/-! ## An attempt with open goals: a function on trees

`Cert` has no leaf for an open goal.  The map out of an attempt at
`Cert.moves` takes one tree for each open goal, by position, to the tree of
the whole. -/

example : Att.mapOut Cert.moves swapAtt ⟨.mk .ax [], .mk .ax [], ⟨⟩⟩ = swapCert := rfl

/-! ## Where a node's equation is decided

`Swap` (`Tactic.lean`) is the system whose judgments hold functions, and
`swapped` an attempt the tactic built there.  Into a type, the kernel does
not evaluate its map out (`MapOut.lean`, `swByTactic`): the instance's
soundness casts along the node's equation.  `Cert.moves` makes no use of
the equation, so the kernel evaluates the tree. -/

open TacticTest in
example : (Att.mapOut Cert.moves swapped ⟨.mk () [], ⟨⟩⟩ == Cert.mk (S := Swap) () [.mk () []]) = true := by
  decide +kernel

/-! ## The tree and the script of one derivation

Two writings of one derivation, each with its checker.  From either, the
other: -/

/-- The script of the same derivation. -/
def swapScript : Script IPC := [⟨0, .impR⟩, ⟨0, .andL p q⟩, ⟨0, .andR⟩, ⟨0, .ax⟩, ⟨0, .ax⟩]

-- the script of the derivation of the tree
example : swapOfCert.script = swapScript := rfl

-- the tree of the derivation of the script
example : ((Der.ofScript swapSeq swapScript (by decide +kernel)).cert == swapCert) = true := by
  decide +kernel

end ProofToolsTest.Explore.CertTest
