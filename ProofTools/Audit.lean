/-
# `ProofTools.Audit`: commands that audit a development

* `ProofTools.Audit.Axioms`: where an axiom enters (`#axiom_path`,
  `#choice_path`, `#choice_sources`), pins that are generated, not retyped
  (`#axiom_pin`, `#axioms_within_pin`), a bound on what a declaration may
  depend on (`#axioms_within`), and a search for library constants free of
  `Classical.choice` (`#cf_search`);
* `ProofTools.Audit.Sweep`: the same bound on every declaration of the
  named libraries (`#axiom_sweep`);
* `ProofTools.Audit.FileBound`: the same bound on every declaration of the
  file it stands in (`#axioms_within_file`, at the end of a theory file);
* `ProofTools.Audit.Rules`: an inductive family printed as inference figures
  (`#rules`), for checking a transcription against its source;
* `ProofTools.Audit.Slime`: computed indices in the conclusions of an
  inductive family's constructors (`#slime`);
* `ProofTools.Audit.Statement`: a declaration's statement and its status,
  PROVED or OPEN, printed for a page that cites it (`#statement`,
  `#statement_status`, `#statement_location`), used by
  `scripts/tutorial_pins.py`.

Core Lean only.  `Axioms`, `Sweep`, `Rules` and `Slime` were carried in
from lax-logic-in-lean (`Meta/`, commit 79d83611) on 2026-11-19; each header
says so.  `FileBound` and `Statement` were written here.  Tests: `ProofToolsTest/`.
-/
import ProofTools.Audit.Axioms
import ProofTools.Audit.Sweep
import ProofTools.Audit.FileBound
import ProofTools.Audit.Rules
import ProofTools.Audit.Slime
import ProofTools.Audit.Statement
