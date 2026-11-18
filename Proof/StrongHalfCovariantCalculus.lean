import Proof.UniformActualStrongHalfCovariantDerivative
import Proof.HalfCovariantSmallScalarProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma half_covariant_strong_smul (d : Data) (f : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hf : ContDiffAt ℝ ∞ f y) (hC : ContDiffAt ℝ ∞ C y)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : halfOperatorCovariantDerivativeL d C H y a=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => f x • C x) (fun x => f x • H x) y a=
      (directionalFDeriv a f y • C y+f y • L).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [halfOperatorCovariantDerivativeL_smul d f C H y a hf hC,hL,
    ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,ContinuousLinearMap.smul_comp]

lemma half_covariant_strong_add (d : Data)
    (C F : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H G : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hF : ContDiffAt ℝ ∞ F y)
    (L M : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : halfOperatorCovariantDerivativeL d C H y a=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hM : halfOperatorCovariantDerivativeL d F G y a=
      M.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => C x+F x) (fun x => H x+G x) y a=
      (L+M).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [halfOperatorCovariantDerivativeL_add d C F H G y a hC hF,hL,hM,ContinuousLinearMap.add_comp]

lemma half_covariant_strong_sum_three (d : Data)
    (C : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hC : ∀ i,ContDiffAt ℝ ∞ (C i) y)
    (L : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : ∀ i,halfOperatorCovariantDerivativeL d (C i) (H i) y a=
      (L i).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => ∑ i : I,C i x) (fun x => ∑ i : I,H i x) y a=
      (∑ i : I,L i).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [halfOperatorCovariantDerivativeL_sum_three d C H y a hC]
  simp_rw [hL]
  apply ContinuousLinearMap.ext
  intro u
  simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply]

/-- The strong extension retains the sharp scalar-weight estimate. -/
lemma norm_strong_half_covariant_weighted_le
    (C L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {f df B Q ε β : ℝ} (hB : 0 ≤ B) (hβ : 0 < β)
    (hf : |f| ≤ B) (hdf : |df| ≤ B*β)
    (hC : ‖C‖ ≤ Q*ε/β) (hL : ‖L‖ ≤ Q*ε) :
    ‖df • C+f • L‖ ≤ (2*B*Q)*ε := by
  calc
    _ ≤ ‖df • C‖+‖f • L‖ := norm_add_le _ _
    _ ≤ (B*β)*(Q*ε/β)+B*(Q*ε) := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hdf hC (norm_nonneg _) (mul_nonneg hB hβ.le))
        (mul_le_mul hf hL (norm_nonneg _) hB)
    _ = _ := by field_simp;ring

end ShrinkingSpheres
