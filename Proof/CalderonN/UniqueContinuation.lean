module

public import Proof.CalderonN.Continuation
import Mathlib.Tactic

/-! Adapted from `Calderon/CollaboratorUniqueContinuationProofOct17.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

/-! # Weak unique continuation

The proof of `uniqueContinuation` (Carleman estimate in `UCPCarleman.lean`, local step and
connectedness in `UCPLocal.lean`) follows Le Rousseau–Lebeau, *On Carleman estimates for elliptic
and parabolic operators*, ESAIM COCV 18 (2012), §§3–4, with an elementary
(Fursikov–Imanuvilov style) integration-by-parts proof of the Carleman estimate. -/

noncomputable section
namespace CalderonN.Carleman

variable {d : ℕ}

/-- Weak unique continuation for `div(A ∇u) = 0`. -/
theorem uniqueContinuation : UniqueContinuation d := UCP.uniqueContinuation_aux

end CalderonN.Carleman
