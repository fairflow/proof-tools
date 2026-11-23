/-
The facts of the corpus, each with its certificate.  Written by `ksearch
facts` (`Main.lean`); do not edit.  The kernel checks every certificate
when this file is elaborated: a tree of moves for a proof in system K, a
finite tree against validity.
-/
import BrunnlerK.Corpus.Basic

namespace BrunnlerK.Corpus.Facts

open BrunnlerK BrunnlerK.Corpus

def ex23 : K (seq[◇(∼a ⋏ ∼b), □a, ◇b]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 4))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.dia
        []
        0
        (BrunnlerK.Form.and (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.atom 5))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.and [0] (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5))
              [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) []),
               ((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 5) [])])])])])

def ex23_formula : K (seq[□(a ⋎ b) ⊃ (□a ⋎ ◇b)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.dia (BrunnlerK.Form.and (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
    (BrunnlerK.Form.or
      (BrunnlerK.Form.box (BrunnlerK.Form.atom 4))
      (BrunnlerK.Form.dia (BrunnlerK.Form.atom 5))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.or
        []
        (BrunnlerK.Form.box (BrunnlerK.Form.atom 4))
        (BrunnlerK.Form.dia (BrunnlerK.Form.atom 5)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 4))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.atom 5))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.dia
                    []
                    0
                    (BrunnlerK.Form.and (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.and [0] (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5))
                      [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) []),
                       ((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 5) [])])])])])])])

def k_axiom : K (seq[□(a ⊃ b) ⊃ (□a ⊃ □b)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.dia (BrunnlerK.Form.and (BrunnlerK.Form.atom 4) (BrunnlerK.Form.natom 5)))
    (BrunnlerK.Form.or
      (BrunnlerK.Form.dia (BrunnlerK.Form.natom 4))
      (BrunnlerK.Form.box (BrunnlerK.Form.atom 5))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.or
        []
        (BrunnlerK.Form.dia (BrunnlerK.Form.natom 4))
        (BrunnlerK.Form.box (BrunnlerK.Form.atom 5)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 5))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.natom 4))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.dia
                    []
                    0
                    (BrunnlerK.Form.and (BrunnlerK.Form.atom 4) (BrunnlerK.Form.natom 5)))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.and [0] (BrunnlerK.Form.atom 4) (BrunnlerK.Form.natom 5))
                      [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) []),
                       ((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 5) [])])])])])])])

def box_and : K (seq[□(a ⋏ b) ⊃ (□a ⋏ □b)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.dia (BrunnlerK.Form.or (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
    (BrunnlerK.Form.and
      (BrunnlerK.Form.box (BrunnlerK.Form.atom 4))
      (BrunnlerK.Form.box (BrunnlerK.Form.atom 5))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.and
        []
        (BrunnlerK.Form.box (BrunnlerK.Form.atom 4))
        (BrunnlerK.Form.box (BrunnlerK.Form.atom 5)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 4))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia
                []
                0
                (BrunnlerK.Form.or (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.or [0] (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5))
                  [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) [])])])]),
       ((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 5))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia
                []
                0
                (BrunnlerK.Form.or (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.or [0] (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5))
                  [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 5) [])])])])])])

def and_box : K (seq[(□a ⋏ □b) ⊃ □(a ⋏ b)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.or
      (BrunnlerK.Form.dia (BrunnlerK.Form.natom 4))
      (BrunnlerK.Form.dia (BrunnlerK.Form.natom 5)))
    (BrunnlerK.Form.box (BrunnlerK.Form.and (BrunnlerK.Form.atom 4) (BrunnlerK.Form.atom 5))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.or
        []
        (BrunnlerK.Form.dia (BrunnlerK.Form.natom 4))
        (BrunnlerK.Form.dia (BrunnlerK.Form.natom 5)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box
            []
            (BrunnlerK.Form.and (BrunnlerK.Form.atom 4) (BrunnlerK.Form.atom 5)))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.natom 4))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.natom 5))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.and [0] (BrunnlerK.Form.atom 4) (BrunnlerK.Form.atom 5))
                      [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) []),
                       ((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 5) [])])])])])])])

def nec_taut : K (seq[□□(a ⋎ ∼a)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.box
    []
    (BrunnlerK.Form.box (BrunnlerK.Form.or (BrunnlerK.Form.atom 4) (BrunnlerK.Form.natom 4))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.box [0] (BrunnlerK.Form.or (BrunnlerK.Form.atom 4) (BrunnlerK.Form.natom 4)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.or [0, 0] (BrunnlerK.Form.atom 4) (BrunnlerK.Form.natom 4))
          [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0, 0] 4) [])])])])

def dia_or : K (seq[◇(a ⋎ b) ⊃ (◇a ⋎ ◇b)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.box (BrunnlerK.Form.and (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
    (BrunnlerK.Form.or
      (BrunnlerK.Form.dia (BrunnlerK.Form.atom 4))
      (BrunnlerK.Form.dia (BrunnlerK.Form.atom 5))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.box [] (BrunnlerK.Form.and (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.or
            []
            (BrunnlerK.Form.dia (BrunnlerK.Form.atom 4))
            (BrunnlerK.Form.dia (BrunnlerK.Form.atom 5)))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.atom 4))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.atom 5))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.and [0] (BrunnlerK.Form.natom 4) (BrunnlerK.Form.natom 5))
                      [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) []),
                       ((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 5) [])])])])])])])

def dual : K (seq[∼(□a) ⊃ ◇(∼a)]) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.box (BrunnlerK.Form.atom 4))
    (BrunnlerK.Form.dia (BrunnlerK.Form.natom 4)))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 4))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.dia [] 0 (BrunnlerK.Form.natom 4))
          [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 4) [])])])])

theorem axiom_4 : ¬ Valid (seq[□a ⊃ □□a]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [BrunnlerK.Tree.node [4] [BrunnlerK.Tree.node [] []]])

theorem axiom_d : ¬ Valid (seq[□p ⊃ ◇p]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [])

theorem axiom_t : ¬ Valid (seq[□p ⊃ p]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [])

theorem axiom_b : ¬ Valid (seq[p ⊃ □◇p]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [0] [BrunnlerK.Tree.node [] []])

theorem axiom_5 : ¬ Valid (seq[◇p ⊃ □◇p]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [BrunnlerK.Tree.node [0] [], BrunnlerK.Tree.node [] []])

theorem box_or : ¬ Valid (seq[□(p ⋎ q) ⊃ (□p ⋎ □q)]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [BrunnlerK.Tree.node [1] [], BrunnlerK.Tree.node [0] []])

theorem dia_and : ¬ Valid (seq[(◇p ⋏ ◇q) ⊃ ◇(p ⋏ q)]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [BrunnlerK.Tree.node [0] [], BrunnlerK.Tree.node [1] []])

theorem empty : ¬ Valid (seq[]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [])

theorem empty_box : ¬ Valid (seq[[]]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [BrunnlerK.Tree.node [] []])

theorem dia_top : ¬ Valid (seq[◇(p ⋎ ∼p)]) :=
  noValid.verdict _ (BrunnlerK.Tree.node [] [])

def boxAnd_4 : K (Corpus.boxAnd 4) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.or
    []
    (BrunnlerK.Form.dia
      (BrunnlerK.Form.or
        (BrunnlerK.Form.or
          (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
          (BrunnlerK.Form.natom 12))
        (BrunnlerK.Form.natom 13)))
    (BrunnlerK.Form.and
      (BrunnlerK.Form.and
        (BrunnlerK.Form.and
          (BrunnlerK.Form.box (BrunnlerK.Form.atom 10))
          (BrunnlerK.Form.box (BrunnlerK.Form.atom 11)))
        (BrunnlerK.Form.box (BrunnlerK.Form.atom 12)))
      (BrunnlerK.Form.box (BrunnlerK.Form.atom 13))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.and
        []
        (BrunnlerK.Form.and
          (BrunnlerK.Form.and
            (BrunnlerK.Form.box (BrunnlerK.Form.atom 10))
            (BrunnlerK.Form.box (BrunnlerK.Form.atom 11)))
          (BrunnlerK.Form.box (BrunnlerK.Form.atom 12)))
        (BrunnlerK.Form.box (BrunnlerK.Form.atom 13)))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.and
            []
            (BrunnlerK.Form.and
              (BrunnlerK.Form.box (BrunnlerK.Form.atom 10))
              (BrunnlerK.Form.box (BrunnlerK.Form.atom 11)))
            (BrunnlerK.Form.box (BrunnlerK.Form.atom 12)))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.and
                []
                (BrunnlerK.Form.box (BrunnlerK.Form.atom 10))
                (BrunnlerK.Form.box (BrunnlerK.Form.atom 11)))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 10))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.dia
                        []
                        0
                        (BrunnlerK.Form.or
                          (BrunnlerK.Form.or
                            (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                            (BrunnlerK.Form.natom 12))
                          (BrunnlerK.Form.natom 13)))
                      [((),
                        ProofTools.Zip.RTree.node
                          (BrunnlerK.Move.or
                            [0]
                            (BrunnlerK.Form.or
                              (BrunnlerK.Form.or
                                (BrunnlerK.Form.natom 10)
                                (BrunnlerK.Form.natom 11))
                              (BrunnlerK.Form.natom 12))
                            (BrunnlerK.Form.natom 13))
                          [((),
                            ProofTools.Zip.RTree.node
                              (BrunnlerK.Move.or
                                [0]
                                (BrunnlerK.Form.or
                                  (BrunnlerK.Form.natom 10)
                                  (BrunnlerK.Form.natom 11))
                                (BrunnlerK.Form.natom 12))
                              [((),
                                ProofTools.Zip.RTree.node
                                  (BrunnlerK.Move.or
                                    [0]
                                    (BrunnlerK.Form.natom 10)
                                    (BrunnlerK.Form.natom 11))
                                  [((),
                                    ProofTools.Zip.RTree.node
                                      (BrunnlerK.Move.ax [0] 10)
                                      [])])])])])]),
               ((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 11))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.dia
                        []
                        0
                        (BrunnlerK.Form.or
                          (BrunnlerK.Form.or
                            (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                            (BrunnlerK.Form.natom 12))
                          (BrunnlerK.Form.natom 13)))
                      [((),
                        ProofTools.Zip.RTree.node
                          (BrunnlerK.Move.or
                            [0]
                            (BrunnlerK.Form.or
                              (BrunnlerK.Form.or
                                (BrunnlerK.Form.natom 10)
                                (BrunnlerK.Form.natom 11))
                              (BrunnlerK.Form.natom 12))
                            (BrunnlerK.Form.natom 13))
                          [((),
                            ProofTools.Zip.RTree.node
                              (BrunnlerK.Move.or
                                [0]
                                (BrunnlerK.Form.or
                                  (BrunnlerK.Form.natom 10)
                                  (BrunnlerK.Form.natom 11))
                                (BrunnlerK.Form.natom 12))
                              [((),
                                ProofTools.Zip.RTree.node
                                  (BrunnlerK.Move.or
                                    [0]
                                    (BrunnlerK.Form.natom 10)
                                    (BrunnlerK.Form.natom 11))
                                  [((),
                                    ProofTools.Zip.RTree.node
                                      (BrunnlerK.Move.ax [0] 11)
                                      [])])])])])])]),
           ((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 12))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.dia
                    []
                    0
                    (BrunnlerK.Form.or
                      (BrunnlerK.Form.or
                        (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                        (BrunnlerK.Form.natom 12))
                      (BrunnlerK.Form.natom 13)))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.or
                        [0]
                        (BrunnlerK.Form.or
                          (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                          (BrunnlerK.Form.natom 12))
                        (BrunnlerK.Form.natom 13))
                      [((),
                        ProofTools.Zip.RTree.node
                          (BrunnlerK.Move.or
                            [0]
                            (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                            (BrunnlerK.Form.natom 12))
                          [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 12) [])])])])])]),
       ((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box [] (BrunnlerK.Form.atom 13))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.dia
                []
                0
                (BrunnlerK.Form.or
                  (BrunnlerK.Form.or
                    (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                    (BrunnlerK.Form.natom 12))
                  (BrunnlerK.Form.natom 13)))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.or
                    [0]
                    (BrunnlerK.Form.or
                      (BrunnlerK.Form.or (BrunnlerK.Form.natom 10) (BrunnlerK.Form.natom 11))
                      (BrunnlerK.Form.natom 12))
                    (BrunnlerK.Form.natom 13))
                  [((), ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [0] 13) [])])])])])])

def nest_6 : K (Corpus.nest 6) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node
  (BrunnlerK.Move.box
    []
    (BrunnlerK.Form.box
      (BrunnlerK.Form.box
        (BrunnlerK.Form.box
          (BrunnlerK.Form.box
            (BrunnlerK.Form.box
              (BrunnlerK.Form.or (BrunnlerK.Form.atom 0) (BrunnlerK.Form.natom 0))))))))
  [((),
    ProofTools.Zip.RTree.node
      (BrunnlerK.Move.box
        [0]
        (BrunnlerK.Form.box
          (BrunnlerK.Form.box
            (BrunnlerK.Form.box
              (BrunnlerK.Form.box
                (BrunnlerK.Form.or (BrunnlerK.Form.atom 0) (BrunnlerK.Form.natom 0)))))))
      [((),
        ProofTools.Zip.RTree.node
          (BrunnlerK.Move.box
            [0, 0]
            (BrunnlerK.Form.box
              (BrunnlerK.Form.box
                (BrunnlerK.Form.box
                  (BrunnlerK.Form.or (BrunnlerK.Form.atom 0) (BrunnlerK.Form.natom 0))))))
          [((),
            ProofTools.Zip.RTree.node
              (BrunnlerK.Move.box
                [0, 0, 0]
                (BrunnlerK.Form.box
                  (BrunnlerK.Form.box
                    (BrunnlerK.Form.or (BrunnlerK.Form.atom 0) (BrunnlerK.Form.natom 0)))))
              [((),
                ProofTools.Zip.RTree.node
                  (BrunnlerK.Move.box
                    [0, 0, 0, 0]
                    (BrunnlerK.Form.box
                      (BrunnlerK.Form.or (BrunnlerK.Form.atom 0) (BrunnlerK.Form.natom 0))))
                  [((),
                    ProofTools.Zip.RTree.node
                      (BrunnlerK.Move.box
                        [0, 0, 0, 0, 0]
                        (BrunnlerK.Form.or (BrunnlerK.Form.atom 0) (BrunnlerK.Form.natom 0)))
                      [((),
                        ProofTools.Zip.RTree.node
                          (BrunnlerK.Move.or
                            [0, 0, 0, 0, 0, 0]
                            (BrunnlerK.Form.atom 0)
                            (BrunnlerK.Form.natom 0))
                          [((),
                            ProofTools.Zip.RTree.node
                              (BrunnlerK.Move.ax [0, 0, 0, 0, 0, 0] 0)
                              [])])])])])])])])

theorem boxOr_4 : ¬ Valid (Corpus.boxOr 4) :=
  noValid.verdict _ (BrunnlerK.Tree.node
  []
  [BrunnlerK.Tree.node [11] [],
   BrunnlerK.Tree.node [10] [],
   BrunnlerK.Tree.node [10] [],
   BrunnlerK.Tree.node [10] []])

def late_4 : K (Corpus.late 4) :=
  treeCert.verdict _ (ProofTools.Zip.RTree.node (BrunnlerK.Move.ax [] 2) [])

end BrunnlerK.Corpus.Facts

#axioms_within_file [propext, Quot.sound]
