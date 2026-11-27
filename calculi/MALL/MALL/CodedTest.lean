/-
Tests of the certifier of saturated sets written in numbers
(`MALL/Coded.lean`, S27): facts with their certificates written by hand,
certificates that are refused, a set of 136 sequents that the check of
sets as lists could not pass in the kernel under 8 GB, and the producer
on the corpus.
-/
import MALL.Encode
import MALL.Corpus.Basic

namespace MALL.CodedTest

open MALL

abbrev a : Form := .atom 0

/-! ## Facts, each with its certificate -/

/-- Contraction: `⊢ a ⊕ a⊥`, with the premises of its two rules.  The
table: `a ⊕ a⊥` (its parts are the next entry and the one after), `a`,
`a⊥`.  In base 5 the three sequents are 1, 5 and 25. -/
def contraction : CodeCert :=
  { B := 5, table := [.plus 0 1, .atom 0, .natom 0], goal := [0],
    tree := .node (.node .leaf 1 .leaf) 5 (.node .leaf 25 .leaf) }

theorem contraction_not_derivable : ¬ Derivable [a ⊕ aᗮ] :=
  noDerivableByCode.verdict _ contraction

theorem contraction_not_valid : ¬ Valid [a ⊕ aᗮ] := noValidByCode.verdict _ contraction

/-- What the numbers stand for. -/
example : contraction.sequents = [[a ⊕ aᗮ], [a], [aᗮ]] := by decide +kernel

/-- "A ⊸ A ⊗ A is not derivable" (Girard, p. 5): `⊢ a⊥ ⅋ (a ⊗ a)`, with
`⊢ a⊥, a ⊗ a` (130 = 125 + 5) and `⊢ a` (25).  The ⊗ stands beside one
formula: of the two ways to divide, each leaves `⊢ a` as a premise. -/
def p5 : CodeCert :=
  { B := 5, table := [.par 2 0, .tensor 0 0, .atom 0, .natom 0], goal := [0],
    tree := .node (.node .leaf 1 .leaf) 25 (.node .leaf 130 .leaf) }

theorem p5_not_derivable : ¬ Derivable [aᗮ ⅋ (a ⊗ a)] := noDerivableByCode.verdict _ p5

example : p5.sequents = [[aᗮ ⅋ (a ⊗ a)], [a], [a ⊗ a, aᗮ]] := by decide +kernel

/-- `⊢ 1, 1`: one sequent, the digit 2 at the place of `1`. -/
def oneOne : CodeCert := { B := 5, table := [.one], goal := [0, 0], tree := .node .leaf 2 .leaf }

theorem one_one : ¬ Derivable [𝟏, 𝟏] := noDerivableByCode.verdict _ oneOne

/-- The finite phase structure. -/
theorem contraction_countermodel : ∃ S : PhaseStructure, S.Finite ∧ ¬ S.Sat [a ⊕ aᗮ] :=
  countermodel_of_code (C := contraction) (by decide +kernel)

/-! ## Certificates that are refused -/

/-- The premise of 2⊕ is missing. -/
theorem missing_premise_rejected :
    codeRefutes { contraction with tree := .node (.node .leaf 1 .leaf) 5 .leaf } [a ⊕ aᗮ] = false := by
  decide +kernel

/-- A member is a logical axiom. -/
theorem axiom_rejected :
    codeRefutes { B := 5, table := [.atom 0, .natom 0], goal := [0, 1], tree := .node .leaf 6 .leaf }
      [a, aᗮ] = false := by decide +kernel

/-- A member is the conclusion of the rule 1. -/
theorem one_rejected :
    codeRefutes { B := 5, table := [.one], goal := [0], tree := .node .leaf 1 .leaf } [𝟏] = false := by
  decide +kernel

/-- A member has ⊤. -/
theorem top_rejected :
    codeRefutes { B := 5, table := [.top, .atom 0], goal := [0, 1], tree := .node .leaf 6 .leaf }
      [⊤, a] = false := by decide +kernel

/-- The sequent is not a member of the set, which is saturated. -/
theorem not_member_rejected : codeRefutes { oneOne with goal := [0] } [𝟏] = false := by
  decide +kernel

/-- The base leaves no room: a digit 2 at base 4. -/
theorem small_base_rejected : codeRefutes { oneOne with B := 4 } [𝟏, 𝟏] = false := by
  decide +kernel

/-- A number with a digit beyond the table (7 = 2 + 1 · 5). -/
theorem beyond_table_rejected :
    codeRefutes { oneOne with tree := .node (.node .leaf 2 .leaf) 7 .leaf } [𝟏, 𝟏] = false := by
  decide +kernel

/-- A part placed beyond the table. -/
theorem part_beyond_rejected :
    codeRefutes { contraction with table := [.plus 0 5, .atom 0, .natom 0] } [a ⊕ aᗮ] = false := by
  decide +kernel

/-- The tree out of order: numbers are not found, and the certificate is
refused (it is not accepted wrongly). -/
theorem disorder_rejected :
    codeRefutes { contraction with tree := .node (.node .leaf 25 .leaf) 5 (.node .leaf 1 .leaf) }
      [a ⊕ aᗮ] = false := by decide +kernel

/-- **The sum of the units is not enough.**  At base 4, four units at
place 0 make the unit of place 1: the number 4 is the sequent `⊢ a⊥`,
which is a saturated set by itself, and `⊢ ⊤, ⊤, ⊤, ⊤` is derivable.  The
check takes the four formulas out of the number one by one, and fails at
the first. -/
theorem carry_rejected :
    codeRefutes { B := 4, table := [.top, .natom 0], goal := [0, 0, 0, 0], tree := .node .leaf 4 .leaf }
      [⊤, ⊤, ⊤, ⊤] = false := by decide +kernel

/-! ## A check stated in parts -/

def leftPart : Tree := .node .leaf 1 .leaf

def rightPart : Tree := .node .leaf 25 .leaf

/-- The certificate of `contraction`, its tree given by two named parts. -/
def contractionParts : CodeCert := { contraction with tree := .node leftPart 5 rightPart }

theorem left_ok : Tree.all contractionParts.memberOK leftPart = true := by decide +kernel

theorem right_ok : Tree.all contractionParts.memberOK rightPart = true := by decide +kernel

theorem five_ok : contractionParts.memberOK 5 = true := by decide +kernel

/-- The check from one theorem for the sequent, one for each part of the
tree and one for the number above them: the form `mallrun prove` writes
for a large set. -/
theorem contraction_by_parts : codeRefutes contractionParts [a ⊕ aᗮ] = true :=
  codeRefutes_of_parts (by decide +kernel) (Tree.all_node left_ok five_ok right_ok)

/-! ## A set beyond the reach of the check of lists -/

/-- `⊢ ((p ⊗ q) & (p ⊗ r))⊥, p ⊗ (q & r)` beside seven copies of ⊥
(`Corpus.bots 7`): a set of 136 sequents, as `mallrun refute bots 7` wrote
it.  Written as lists and checked by `refutedBy`, the kernel was stopped
at 8 GB after 87 s (`campaign/measurements.md`). -/
theorem bots7 : ¬ Derivable (Corpus.bots 7) :=
  noDerivableByCode.verdict _
  { B := 11
    table := [.plus 1 2, .tensor 3 2, .par 5 6, .par 4 6, .wth 1 2, .atom 0, .atom 1, .atom 2, .natom 0, .natom 1, .natom 2, .bot]
    goal := [0, 1, 11, 11, 11, 11, 11, 11, 11]
    tree := (.node (.node (.node (.node (.node (.node (.node (.node .leaf 12 .leaf) 132 .leaf) 1342 (.node .leaf 161051 .leaf)) 161052 (.node (.node .leaf 161172 .leaf) 162382 (.node .leaf 2357962332 .leaf))) 2358108742 (.node (.node (.node (.node .leaf 2377434862 .leaf) 2572306583 .leaf) 2572467623 (.node .leaf 25937439242 .leaf)) 25937585652 (.node (.node .leaf 25939196162 .leaf) 26151783493 (.node .leaf 26151944533 .leaf)))) 285311670623 (.node (.node (.node (.node (.node .leaf 285311670743 .leaf) 285311671953 .leaf) 285311831662 (.node .leaf 285311831663 .leaf)) 285311831783 (.node (.node .leaf 285311832993 .leaf) 287669632943 (.node .leaf 287669779353 .leaf))) 287689105473 (.node (.node (.node .leaf 287883977194 .leaf) 287884138234 (.node .leaf 311249109853 .leaf)) 311249256263 (.node (.node .leaf 311250866773 .leaf) 311463454104 (.node .leaf 311463615144 .leaf))))) 570623341234 (.node (.node (.node (.node (.node (.node .leaf 570623341354 .leaf) 570623342564 .leaf) 570623502273 (.node .leaf 570623502274 .leaf)) 570623502394 (.node (.node .leaf 570623503604 .leaf) 572981303554 (.node .leaf 572981449964 .leaf))) 573000776084 (.node (.node (.node .leaf 573195647805 .leaf) 573195808845 (.node .leaf 596560780464 .leaf)) 596560926874 (.node (.node .leaf 596562537384 .leaf) 596775124715 (.node .leaf 596775285755 .leaf)))) 855935011845 (.node (.node (.node (.node (.node .leaf 855935011965 .leaf) 855935013175 .leaf) 855935172884 (.node .leaf 855935172885 .leaf)) 855935173005 (.node (.node .leaf 855935174215 .leaf) 858292974165 (.node .leaf 858293120575 .leaf))) 858312446695 (.node (.node (.node .leaf 858507318416 .leaf) 858507479456 (.node .leaf 881872451075 .leaf)) 881872597485 (.node (.node .leaf 881874207995 .leaf) 882086795326 (.node .leaf 882086956366 .leaf)))))) 1141246682456 (.node (.node (.node (.node (.node (.node (.node .leaf 1141246682576 .leaf) 1141246683786 .leaf) 1141246843495 (.node .leaf 1141246843496 .leaf)) 1141246843616 (.node (.node .leaf 1141246844826 .leaf) 1143604644776 (.node .leaf 1143604791186 .leaf))) 1143624117306 (.node (.node (.node .leaf 1143818989027 .leaf) 1143819150067 (.node .leaf 1167184121686 .leaf)) 1167184268096 (.node (.node .leaf 1167185878606 .leaf) 1167398465937 (.node .leaf 1167398626977 .leaf)))) 1426558353067 (.node (.node (.node (.node (.node .leaf 1426558353187 .leaf) 1426558354397 .leaf) 1426558514106 (.node .leaf 1426558514107 .leaf)) 1426558514227 (.node (.node .leaf 1426558515437 .leaf) 1428916315387 (.node .leaf 1428916461797 .leaf))) 1428935787917 (.node (.node (.node .leaf 1429130659638 .leaf) 1429130820678 (.node .leaf 1452495792297 .leaf)) 1452495938707 (.node (.node .leaf 1452497549217 .leaf) 1452710136548 (.node .leaf 1452710297588 .leaf))))) 1711870023678 (.node (.node (.node (.node (.node (.node .leaf 1711870023798 .leaf) 1711870025008 .leaf) 1711870184717 (.node .leaf 1711870184718 .leaf)) 1711870184838 (.node (.node .leaf 1711870186048 .leaf) 1714227985998 (.node .leaf 1714228132408 .leaf))) 1714247458528 (.node (.node (.node .leaf 1714442330249 .leaf) 1714442491289 (.node .leaf 1737807462908 .leaf)) 1737807609318 (.node (.node .leaf 1737809219828 .leaf) 1738021807159 (.node .leaf 1738021968199 .leaf)))) 1997181694289 (.node (.node (.node (.node (.node .leaf 1997181694409 .leaf) 1997181695619 .leaf) 1997181855328 (.node .leaf 1997181855329 .leaf)) 1997181855449 (.node (.node .leaf 1997181856659 .leaf) 1999539656609 (.node .leaf 1999539803019 .leaf))) 1999559129139 (.node (.node (.node .leaf 1999754000860 .leaf) 1999754161900 (.node .leaf 2023119133519 .leaf)) 2023119279929 (.node (.node .leaf 2023120890439 .leaf) 2023333477770 (.node .leaf 2023333638810 .leaf))))))) }

/-! ## The producer, on the corpus -/

/-- For each entry with no derivation: the producer's set, written in
numbers, passes; and the sequents that the numbers stand for pass the
check of sets (S27, on instances). -/
def producerOK : Bool :=
  (Corpus.entries.filter (!·.derivable)).all fun e =>
    match refuteSet e.seq with
    | some D =>
      let C := Encode.encode D e.seq
      codeRefutes C e.seq && refutedBy C.sequents e.seq && C.sequents.length == D.length
    | none => false

#guard producerOK
#guard (Corpus.entries.filter (!·.derivable)).length == 15

-- The two families that the measurements use.
#guard (List.range 5).all fun n =>
  match refuteSet (Corpus.bots n) with
  | some D => codeRefutes (Encode.encode D (Corpus.bots n)) (Corpus.bots n) && D.length == 17 * (n + 1)
  | none => false

#guard (List.range 4).all fun n =>
  match refuteSet (Corpus.parBots n) with
  | some D => codeRefutes (Encode.encode D (Corpus.parBots n)) (Corpus.parBots n)
  | none => false

end MALL.CodedTest
