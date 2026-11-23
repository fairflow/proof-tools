/-
# `ProofTools.Explore.Panel`: an attempt drawn as a tree in the infoview

**A trial** (2026-11-21), off unless `set_option walk.panel true`.  With it
on, `#walk d …` also shows a panel in the infoview while the editor's
cursor is on the command:

    Walk: at 0.0
    [down 0] [down 1] [up] [top] [goal 0]
    ▾  ⊢ ((p0 ∧ p1) → (p1 ∧ p0))   by impR
      ▾ (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andL p0 p1
        ▾ p0, p1, (p0 ∧ p1) ⊢ (p1 ∧ p0)   by andR            the focus
            0: ? p0, p1, (p0 ∧ p1) ⊢ p1
            1: p0, p1, (p0 ∧ p1) ⊢ p0   by ax   [closed]
    at 0.0: 2 premises; open goals: 1 under the focus, 0 left of it, 1 in all.  write into the file

* The whole attempt is there as a tree.  A node's premises are drawn if it
  is on the way to the focus or is the focus; `▸` and `▾` show and hide the
  premises of any node, where a hidden part says `[closed]` or `[n open]`.
* At a focus the panel says what the view of `#walk` says there
  (`Walk.lean`): the buttons are the motions that can be made, in the order
  they are offered (`Cursor.motions`); the rows from the root to the focus,
  and the premises of the focus with their numbers and `[closed]` or
  `[n open]`, are the lines of `Cursor.view`; the last line is
  `Cursor.viewFoot`.  The script computes these again from the tree, so a
  change to one of them in Lean is to be made in the script too.
* A click on a button, or on a node, puts the focus there.
  The panel keeps the focus: nothing is written to the file.
* `write into the file` replaces the motions of the `#walk` by the path to
  the focus (`down i …`), so that the file's walk, its view and the panel
  agree again.  When the motions in the file change, the panel follows.

What Lean sends is `walkPanelData d ms`: the attempt as a tree of text
(`Att.tree`: at each node the judgment and the move through the instance's
printers, and the premises) and the address the motions reach.  The script
that draws it is `walkPanel.js`, beside this file.

Code for the editor: nothing here is trusted, and nothing is proved here.
The panel shows the same data as the view; it has no part in what a
motion is (`Motion.lean`).

Core Lean only (`Lean.Widget`); the script is JavaScript, run by the
infoview with its own React.
-/
import Lean
import ProofTools.Explore.Motion
import ProofTools.Explore.Tactic

namespace ProofTools.Explore

open Lean

variable {S : ProofSystem}

mutual
/-- **An attempt as a tree of text**: at each node the judgment (`j`), the
move (`m`; none at an open goal) and the premises (`kids`). -/
def Att.tree [E : Explorable S] : {o : Bool} → {j : S.Judg} → Att S o j → Json
  | _, j, .goal => Json.mkObj [("j", E.showJudg j), ("kids", Json.arr #[])]
  | _, j, .node m _ _ ds =>
    Json.mkObj [("j", E.showJudg j), ("m", E.showMove m), ("kids", Json.arr ds.trees.toArray)]
/-- `Att.tree` on a list. -/
def Atts.trees [E : Explorable S] : {o : Bool} → {ps : List S.Judg} → Atts S o ps → List Json
  | _, _, .nil => []
  | _, _, .cons d ds => d.tree :: ds.trees
end

/-- The cursor after the motions of `ms` that can be made, up to the first
that cannot. -/
def Cursor.movesWhile {j : S.Judg} (c : Cursor S j) (ms : List Motion) : Cursor S j :=
  (Cursor.trail 0 c ms).last

/-- **What the panel is given**, as JSON text: the attempt `d` as a tree
(`tree`), and the address that the motions `ms` reach from its root
(`focus`; if one cannot be made, the address before it). -/
def walkPanelData [Explorable S] {o : Bool} {j : S.Judg} (d : Att S o j) (ms : List Motion) :
    String :=
  (Json.mkObj [("tree", d.tree),
    ("focus", toJson ((Cursor.ofAtt d).movesWhile ms).addr)]).compress

/-- The script of the panel. -/
@[widget_module]
def walkPanelModule : Widget.Module where
  javascript := include_str "walkPanel.js"

end ProofTools.Explore
