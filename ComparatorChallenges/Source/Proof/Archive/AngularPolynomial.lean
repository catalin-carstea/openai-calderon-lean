module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/- Adopted with module headers from Proposition 5.3 release f308cb9d. -/
/- Adapted from the selected ZIP, lean/Calderon/AngularPolynomial.lean.
   Proof bodies and mathematical declarations are preserved. Local import paths are rewritten. -/

@[expose] public section

noncomputable section

namespace OAI.AnisotropicCalderon.AngularPolynomial

open MvPolynomial

variable {σ : Type*} [Fintype σ]

def laplacian (q : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, pderiv i (pderiv i q)

lemma laplacian_C_mul (c : ℝ) (q : MvPolynomial σ ℝ) :
    laplacian (C c * q) = C c * laplacian q := sorry

end OAI.AnisotropicCalderon.AngularPolynomial
