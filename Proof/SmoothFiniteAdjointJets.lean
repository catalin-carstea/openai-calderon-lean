import Proof.SmoothFiniteJetBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
open scoped ContDiff
namespace ShrinkingSpheres.SmoothFiniteJetBound
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
lemma adjoint {A : P → E →L[ℝ] F} {p : P} {N : ℕ} {B : ℝ}
    (hA : SmoothFiniteJetBound A p N B) :
    SmoothFiniteJetBound (fun x => (A x).adjoint) p N B := by
  let J := (ContinuousLinearMap.adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E))
  refine ⟨hA.nonneg,J.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=A) p hA.smooth,?_⟩
  intro n hn
  change ‖iteratedFDeriv ℝ n (J ∘ A) p‖ ≤ B
  rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  exact hA.bound n hn
end ShrinkingSpheres.SmoothFiniteJetBound
