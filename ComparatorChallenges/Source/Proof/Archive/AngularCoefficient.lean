module

public import Proof.Archive.FischerPolynomial
import Mathlib.Tactic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/- Adopted with module headers from Proposition 5.3 release f308cb9d. -/
/- Adapted from the selected ZIP, lean/Calderon/AngularCoefficient.lean.
   Proof bodies and mathematical declarations are preserved. Local import paths are rewritten. -/

@[expose] public section

noncomputable section
namespace OAI.AnisotropicCalderon.AngularPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ]

def sphereNormalization (n k : ℕ) : ℝ := ∏ j ∈ Finset.range k, ((n : ℝ) + 2 * (j : ℝ))

def normalizedFischerInner (k : ℕ) (p q : MvPolynomial σ ℝ) : ℝ :=
  fischerInner p q / sphereNormalization (Fintype.card σ) k

end OAI.AnisotropicCalderon.AngularPolynomial
