module

public import Proof.Archive.AngularPolynomial
import Mathlib.Tactic

/- Adopted with module headers from Proposition 5.3 release f308cb9d. -/
/- Adapted from the selected ZIP, lean/Calderon/FischerPolynomial.lean.
   Proof bodies and mathematical declarations are preserved. Local import paths are rewritten. -/

@[expose] public section

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def fischerWeight (a : σ →₀ ℕ) : ℝ := ∏ i : σ, (Nat.factorial (a i) : ℝ)

def fischerInner (p q : MvPolynomial σ ℝ) : ℝ :=
  p.coeff.sum fun a c => c * q.coeff a * fischerWeight a

end OAI.AnisotropicCalderon.AngularPolynomial
