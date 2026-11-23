/-
Tests of the zipper of rose trees (`ProofTools.Zipper.Rose`, `RoseIndexed`,
`RoseUpdate`, `RoseRender`): every move and every edit, on Huet's parse tree
and on a binary tree.

1. Huet (1997), §2: the parse tree of `a * b + c * d`, unlabelled edges,
   navigation by position; the edits at the focus.
2. A full binary tree, as a rose tree with edges `false` (left) and `true`
   (right), each node labelled by its address read as a binary number:
   navigation by edge and by address, lookups, updating at an address.
3. The indexed zipper on the same tree: the address in the type, `up` total.

Every check is a `#guard` or a pinned `#guard_msgs`.
-/
import ProofTools.Zipper.RoseIndexed
import ProofTools.Zipper.RoseUpdate
import ProofTools.Zipper.RoseRender

namespace ProofToolsTest.Zipper.RoseTest

open ProofTools ProofTools.Zip

/-- Print a zipper, or say there is none. -/
def show? {κ α : Type} (ek : κ → String) (ea : α → String) : Option (Zipper κ α) → IO Unit
  | some z => IO.println (z.drawWith ek ea)
  | none => IO.println "no such position"

/-! ## 1. Huet's parse tree -/

/-- Huet's leaves. -/
def item (s : String) : RTree Unit String := .leaf s
/-- Huet's sections: nodes labelled `§`, unlabelled edges. -/
def sec (ts : List (RTree Unit String)) : RTree Unit String := .node "§" (ts.map ((), ·))

/-- `a * b + c * d`. -/
def expr : RTree Unit String :=
  sec [sec [item "a", item "*", item "b"], item "+", sec [item "c", item "*", item "d"]]

/-- Huet's moves to the second `*`: down, right, right, down, right. -/
def secondStar : Option (Zipper Unit String) :=
  (Zipper.ofTree expr).downAt 0 >>= Zipper.right >>= Zipper.right >>= Zipper.downAt 0
    >>= Zipper.right

#guard secondStar.map Zipper.label == some "*"
-- The path: the crumb at `c * d` (left `c`, right `d`), then the root crumb.
#guard (secondStar.map fun z => z.path.map fun c => (c.left.map (·.2.label), c.right.map (·.2.label)))
  == some [(["c"], ["d"]), (["+", "§"], [])]
-- Moving changes nothing.
#guard secondStar.map Zipper.toTree == some expr
-- With unlabelled edges the address says only how deep the focus is.
#guard secondStar.map Zipper.addr == some [(), ()]

/--
info: §
    • ↦ §
        • ↦ a
        • ↦ *
        • ↦ b
    • ↦ +
    • ↦ §
        • ↦ c
        • ↦ ▶ *
        • ↦ d
-/
#guard_msgs in
#eval show? (fun _ => "•") id secondStar

/-! ### The moves -/

-- `left` and `right`, and where they end.
#guard (secondStar.bind Zipper.left).map Zipper.label == some "c"
#guard ((secondStar.bind Zipper.left).bind Zipper.left).isNone
#guard (secondStar.bind Zipper.right).map Zipper.label == some "d"
#guard ((secondStar.bind Zipper.right).bind Zipper.right).isNone
#guard ((secondStar.bind Zipper.left).bind Zipper.right).map Zipper.label == some "*"
-- `up`, to the root and no further.
#guard (secondStar.bind Zipper.up).map (·.focus) == some (sec [item "c", item "*", item "d"])
#guard ((secondStar.bind Zipper.up).bind Zipper.up).map (·.focus) == some expr
#guard ((secondStar.bind Zipper.up).bind Zipper.up).map Zipper.atRoot == some true
#guard (((secondStar.bind Zipper.up).bind Zipper.up).bind Zipper.up).isNone
#guard secondStar.map Zipper.atRoot == some false
-- `top`, in one step.
#guard secondStar.map (fun z => (z.top.focus, z.top.atRoot)) == some (expr, true)
-- `downAt`, past the last child.
#guard ((Zipper.ofTree expr).downAt 2).map (·.focus) == some (sec [item "c", item "*", item "d"])
#guard ((Zipper.ofTree expr).downAt 3).isNone
-- `down` and `descend` along the edge `()` take the first child.
#guard ((Zipper.ofTree expr).down ()).map (·.focus) == some (sec [item "a", item "*", item "b"])
#guard ((Zipper.ofTree expr).descend [(), ()]).map Zipper.label == some "a"
#guard (Zipper.goto expr [(), (), ()]).isNone

/-! ### The edits at the focus -/

-- `modify`: the label.
#guard (secondStar.map fun z => (z.modify fun _ => "/").toTree)
  == some (sec [sec [item "a", item "*", item "b"], item "+", sec [item "c", item "/", item "d"]])
-- `replace`: the subtree.
#guard (secondStar.map fun z => (z.replace (sec [item "e", item "f"])).toTree)
  == some (sec [sec [item "a", item "*", item "b"], item "+",
      sec [item "c", sec [item "e", item "f"], item "d"]])
-- `addChild`: a last child of the focus.
#guard ((Zipper.ofTree expr).addChild () (item "!")).toTree
  == sec [sec [item "a", item "*", item "b"], item "+", sec [item "c", item "*", item "d"], item "!"]
-- `insertLeft` and `insertRight`: the focus stays; there is no sibling of the root.
#guard ((secondStar.bind (Zipper.insertLeft () (item "x"))).map fun z => (z.label, z.toTree))
  == some ("*", sec [sec [item "a", item "*", item "b"], item "+",
      sec [item "c", item "x", item "*", item "d"]])
#guard ((secondStar.bind (Zipper.insertRight () (item "y"))).map fun z => (z.label, z.toTree))
  == some ("*", sec [sec [item "a", item "*", item "b"], item "+",
      sec [item "c", item "*", item "y", item "d"]])
#guard ((Zipper.ofTree expr).insertLeft () (item "x")).isNone
#guard ((Zipper.ofTree expr).insertRight () (item "y")).isNone
-- Huet's `delete` moves the focus to the right sibling,
#guard ((secondStar.bind Zipper.delete).map fun z => (z.label, z.toTree))
  == some ("d", sec [sec [item "a", item "*", item "b"], item "+", sec [item "c", item "d"]])
-- or else to the left sibling,
#guard (((secondStar.bind Zipper.right).bind Zipper.delete).map fun z => (z.label, z.toTree))
  == some ("*", sec [sec [item "a", item "*", item "b"], item "+", sec [item "c", item "*"]])
-- or else to the parent; the root cannot be deleted.
#guard (((Zipper.ofTree (sec [item "a"])).downAt 0 >>= Zipper.delete).map fun z =>
    (z.label, z.atRoot, z.toTree)) == some ("§", true, sec [])
#guard (Zipper.ofTree expr).delete.isNone

/-! ## 2. A binary tree with labelled edges -/

/-- The full binary tree of depth `n`: edge `false` to the left child, `true`
to the right.  Each node is labelled by its address read as a binary number
(with a leading `1`). -/
def full : Nat → Nat → RTree Bool Nat
  | 0, m => .leaf m
  | n + 1, m => .node m [(false, full n (2 * m)), (true, full n (2 * m + 1))]

/-- Depth 3: 15 nodes, labelled 1 to 15. -/
def t3 : RTree Bool Nat := full 3 1

/-! ### Navigation by edge and by address -/

#guard ((Zipper.ofTree t3).down true).map Zipper.label == some 0b11
#guard ((Zipper.ofTree t3).down true >>= Zipper.descend [false, false]).map Zipper.label
  == some 0b1100
#guard ((Zipper.ofTree t3).down true >>= Zipper.up).map (·.focus) == some t3
#guard (Zipper.goto t3 [false, true]).map Zipper.label == some 0b101
-- `goto_addr`: the address is the one asked for, in the same tree.
#guard (Zipper.goto t3 [false, true]).map Zipper.addr == some [false, true]
#guard (Zipper.goto t3 [false, true]).map Zipper.toTree == some t3
#guard (Zipper.goto t3 [true, true, true, true]).isNone
-- `goto_focus`: the focus is the subtree at the address.
#guard (Zipper.goto t3 [true, false]).map (·.focus) == t3.get? [true, false]
#guard t3.get? [] == some t3
#guard t3.at? [true, false] == some 0b110
#guard t3.at? [true, false, true, true] == none
-- `left` and `right` keep all of the address but its last edge.
#guard ((Zipper.goto t3 [false, true]).bind Zipper.left).map Zipper.addr == some [false, false]

/-- Go to `[false, true]` and set its label to `0`. -/
def newFocus : Option (Zipper Bool Nat) :=
  (Zipper.goto t3 [false, true]).map (Zipper.modify fun _ => 0)

/-- Then go up and add `100` to the label there. -/
def newFocus2 : Option (Zipper Bool Nat) :=
  (newFocus.bind Zipper.up).map (Zipper.modify fun m => m + 100)

#guard newFocus.map Zipper.addr == some [false, true]
#guard newFocus2.map Zipper.addr == some [false]
#guard newFocus2.map (fun z => z.toTree.at? [false]) == some (some 102)
#guard newFocus2.map (fun z => z.toTree.at? [false, true]) == some (some 0)

/--
info: 1
    L ↦ 102
        L ↦ 4
            L ↦ 8
            R ↦ 9
        R ↦ ▶ 0
            L ↦ 10
            R ↦ 11
    R ↦ 3
        L ↦ 6
            L ↦ 12
            R ↦ 13
        R ↦ 7
            L ↦ 14
            R ↦ 15
-/
#guard_msgs in
#eval show? (fun b => if b then "R" else "L") toString (newFocus2.bind (Zipper.down true))

/-- A new child of a leaf. -/
def attached : Option (RTree Bool Nat) :=
  (Zipper.goto t3 [false, false, false]).map fun z => (z.addChild false (.leaf 0)).toTree

#guard (attached.bind (·.get? [false, false, false, false])).map RTree.label == some 0

/-! ### Lists of children: the first pair with a key -/

#guard find? 2 [(1, "a"), (2, "b"), (3, "c"), (2, "d")] == some "b"
#guard find? 4 [(1, "a"), (2, "b"), (3, "c"), (2, "d")] == none
#guard splitKey 2 [(1, "a"), (2, "b"), (3, "c"), (2, "d")]
  == some ([(1, "a")], "b", [(3, "c"), (2, "d")])
#guard updFirst 2 (· ++ "!") [(1, "a"), (2, "b"), (3, "c"), (2, "d")]
  == [(1, "a"), (2, "b!"), (3, "c"), (2, "d")]

/-- Two children along one edge. -/
def twins : RTree Bool Nat := .node 0 [(false, .leaf 1), (false, .leaf 2)]

-- `down` takes the first; the second is reached by position, and has the
-- same address.
#guard ((Zipper.ofTree twins).down false).map Zipper.label == some 1
#guard ((Zipper.ofTree twins).downAt 1).map (fun z => (z.label, z.addr)) == some (2, [false])
-- Up from the second and down its edge again lands on the first: `down_up`
-- of the indexed zipper asks for a canonical path, and this is why.
#guard ((Zipper.ofTree twins).downAt 1 >>= Zipper.up >>= Zipper.down false).map Zipper.label
  == some 1

/-! ### Updating at an address -/

/-- Cut the subtree at `[true, false]` down to a leaf `0`. -/
def cut : RTree Bool Nat := t3.updateAt (fun _ => .leaf 0) [true, false]

#guard cut.at? [true, false] == some 0
#guard cut.get? [true, false, false] == none
-- `at_updateAt_of_not_prefix`: labels away from the address are unchanged.
#guard cut.at? [true, true] == t3.at? [true, true]
#guard cut.at? [true] == t3.at? [true]
-- No node at the address: nothing changes.
#guard t3.updateAt (fun _ => .leaf 0) [true, true, true, true] == t3
-- The same change made through the zipper.  (Checked on this tree; no
-- theorem of the library relates `updateAt` to `goto` and `replace`.)
#guard (Zipper.goto t3 [true, false]).map (fun z => (z.replace (.leaf 0)).toTree) == some cut

/-! ### Comparing, relabelling, drawing -/

#guard t3 == t3
#guard t3 != full 3 2
#guard cut != t3
#guard (full 1 1).map (· + 1) == .node 2 [(false, .leaf 3), (true, .leaf 4)]
#guard (full 1 1).draw == "1\n    false ↦ 2\n    true ↦ 3"
#guard ((Zipper.ofTree (full 1 1)).down true).map Zipper.draw
  == some "1\n    false ↦ 2\n    true ↦ ▶ 3"

/-! ## 3. The indexed zipper -/

/-- The address `[false, true]` is in the type (reversed: `[true, false]`). -/
def atFT : Option (IZipper Bool Nat [true, false]) := IZipper.goto t3 [false, true]

/-- Two steps up from depth two: total, no `Option`. -/
def upTwo (z : IZipper Bool Nat [true, false]) : IZipper Bool Nat [] := z.up.up

#guard atFT.map (·.focus.label) == some 0b101
#guard atFT.map (fun z => (upTwo z).focus.label) == some 1
#guard atFT.map IZipper.addr == some [false, true]
#guard atFT.map IZipper.toTree == some t3
-- Indexed and plain navigation agree (`forget_goto`).
#guard (atFT.map IZipper.forget).map Zipper.label == (Zipper.goto t3 [false, true]).map Zipper.label
#guard (atFT.map IZipper.forget).map Zipper.addr == some [false, true]
-- `down` and `descend`.
#guard ((IZipper.ofTree t3).down true).map (·.focus.label) == some 0b11
#guard ((IZipper.ofTree t3).descend [true, false]).map (·.focus.label) == some 0b110
#guard (IZipper.goto t3 [true, true, true, true]).isNone
-- `left` and `right` return the sibling's edge with the zipper.
#guard (atFT.bind IZipper.left).map (fun x => (x.1, x.2.focus.label)) == some (false, 0b100)
#guard (atFT.bind IZipper.right).isNone
#guard ((atFT.bind IZipper.left).bind fun x => x.2.right).map (fun x => (x.1, x.2.focus.label))
  == some (true, 0b101)
-- `modify` and `replace`.
#guard atFT.map (fun z => (z.modify fun _ => 0).toTree.at? [false, true]) == some (some 0)
#guard atFT.map (fun z => (z.replace (.leaf 0)).toTree)
  == some (t3.updateAt (fun _ => .leaf 0) [false, true])
-- A plain zipper indexed by its own path, and back (`Zipper.forget_index`).
#guard (Zipper.goto t3 [false, true]).map (fun z => (z.index.focus.label, z.index.forget.addr))
  == some (0b101, [false, true])

end ProofToolsTest.Zipper.RoseTest
