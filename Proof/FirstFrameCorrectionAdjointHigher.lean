import Proof.PrincipalFirstDerivativeHalfCoefficient
import Proof.LowBoundedCorrectionAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def firstFrameCorrectionAdjointHigherL (d : Data) (y : X) (i : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i).adjoint.comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

/-- The physical graph is proved by transposing the genuine inclusion;
no identification of the Sobolev carriers is used as a regularity claim. -/
lemma firstFrameCorrectionAdjointHigherL_balanced (d : Data) (y : X) (i : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (firstFrameCorrectionAdjointHigherL d y i)=
    (firstFrameLowerCorrectionL d y i).adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [firstFrameLowerCorrectionL,ContinuousLinearMap.adjoint_comp,
    sphereSobolevHalfNegativeInclusion_adjoint,ContinuousLinearMap.comp_assoc]
  rfl

lemma norm_firstFrameCorrectionAdjointHigherL_le (d : Data) (y : X) (i : I) :
    ‖firstFrameCorrectionAdjointHigherL d y i‖ ≤ ‖firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq
      (by rw [mul_one,ContinuousLinearMap.adjoint.norm_map]))

lemma Admissible.contDiffOn_firstFrameCorrectionAdjointHigherL {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (i : I) :
    ContDiffOn ℝ ∞ (fun y => firstFrameCorrectionAdjointHigherL d y i) Y := by
  let Adj : (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact (Adj.contDiff.comp_contDiffOn
    (hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK (-(1/2:ℝ)) i)).clm_comp contDiffOn_const
end ShrinkingSpheres
