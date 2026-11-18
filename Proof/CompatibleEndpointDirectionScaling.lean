import Proof.Archive.SphereSobolevInclusion
import Proof.BoundedCompositionCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Unit-direction compatible endpoints extend to every direction of the
    SAME coarse continuous linear family, with its exact norm factor. -/
lemma compatible_endpoints_all_directions
    (S : P →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0)) (C : ℝ)
    (hUnit : ∀ b : P,‖b‖ ≤ 1 →
      ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b)=
          Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
          (S b).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        ‖Lo‖ ≤ C ∧ ‖Hi‖ ≤ C) (b : P) :
    ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S b)=
        Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
        (S b).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
      ‖Lo‖ ≤ C*‖b‖ ∧ ‖Hi‖ ≤ C*‖b‖ := by
  by_cases hb : b=0
  · subst b
    exact ⟨0,0,by simp,by simp,by simp,by simp⟩
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  let u := (‖b‖)⁻¹ • b
  have hNorm : ‖u‖=1 := by
    dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg b),inv_mul_cancel₀ hn]
  obtain ⟨Lo,Hi,hL,hH,hLN,hHN⟩ := hUnit u hNorm.le
  have hbScale : ‖b‖ • u=b := by
    dsimp only [u]
    exact smul_inv_smul₀ hn b
  have hSb : S b=‖b‖ • S u := (congrArg S hbScale.symm).trans (S.map_smul _ u)
  refine ⟨‖b‖ • Lo,‖b‖ • Hi,?_,?_,?_,?_⟩
  · calc
      _ = (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (‖b‖ • S u) :=
        congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T) hSb
      _ = _ := by
        simpa only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp] using
          congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => ‖b‖ • T) hL
  · have h := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => ‖b‖ • T) hH
    have h' : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (‖b‖ • Hi)=
        (‖b‖ • S u).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
      simpa only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp] using h
    exact h'.trans (congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hSb.symm)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
    exact (mul_le_mul_of_nonneg_left hLN (norm_nonneg b)).trans_eq (mul_comm _ _)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
    exact (mul_le_mul_of_nonneg_left hHN (norm_nonneg b)).trans_eq (mul_comm _ _)
end ShrinkingSpheres
