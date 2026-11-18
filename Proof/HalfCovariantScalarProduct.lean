import Proof.PhysicalHalfCovariantGreenBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The literal covariant derivative obeys the scalar Leibniz rule for
    the SAME lower and higher families. This serves the weighted physical
    first-base coefficients, without replacing parameter germs by constants. -/
lemma halfOperatorCovariantDerivativeL_smul (d : Data) (f : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hf : ContDiffAt ℝ ∞ f y) (hC : ContDiffAt ℝ ∞ C y) :
    halfOperatorCovariantDerivativeL d (fun x => f x • C x) (fun x => f x • Ch x) y a=
      directionalFDeriv a f y • (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))+
      f y • halfOperatorCovariantDerivativeL d C Ch y a := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have heq : (fun x => (f x • C x).comp J)=(fun x => f x • (C x).comp J) := rfl
  have hD := OperatorForms.directional_smul_at f (fun x => (C x).comp J) y a hf
    (hC.clm_comp contDiffAt_const)
  unfold halfOperatorCovariantDerivativeL
  simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul]
  rw [hD]
  apply ContinuousLinearMap.ext
  intro u
  simp only [halfOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.sub_apply,_root_.smul_apply,map_smul]
  module

/-- Relative scalar derivative bounds preserve exactly the epsilon/beta
    and epsilon weights needed by the physical Green estimate. -/
lemma norm_halfOperatorCovariantDerivativeL_smul_le (d : Data) (f : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hf : ContDiffAt ℝ ∞ f y) (hC : ContDiffAt ℝ ∞ C y)
    {B Q eps β : ℝ} (hB : 0 ≤ B) (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hβ : 0 < β)
    (hF : |f y| ≤ B) (hdF : |directionalFDeriv a f y| ≤ B*β)
    (hCN : ‖C y‖ ≤ Q*eps/β) (hDC : ‖halfOperatorCovariantDerivativeL d C Ch y a‖ ≤ Q*eps) :
    ‖halfOperatorCovariantDerivativeL d (fun x => f x • C x) (fun x => f x • Ch x) y a‖ ≤
      (2*B*Q)*eps := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hCJ : ‖(C y).comp J‖ ≤ Q*eps/β :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg (C y))).trans_eq
        (mul_one _)).trans hCN)
  rw [halfOperatorCovariantDerivativeL_smul d f C Ch y a hf hC]
  calc
    _ ≤ ‖directionalFDeriv a f y • (C y).comp J‖+
        ‖f y • halfOperatorCovariantDerivativeL d C Ch y a‖ := norm_add_le _ _
    _ ≤ (B*β)*(Q*eps/β)+B*(Q*eps) := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hdF hCJ (norm_nonneg _) (mul_nonneg hB hβ.le))
        (mul_le_mul hF hDC (norm_nonneg _) hB)
    _ = _ := by field_simp;ring
lemma halfOperatorCovariantDerivativeL_sum_three (d : Data)
    (C : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hC : ∀ i,ContDiffAt ℝ ∞ (C i) y) :
    halfOperatorCovariantDerivativeL d (fun x => ∑ i : I,C i x) (fun x => ∑ i : I,Ch i x) y a=
      ∑ i : I,halfOperatorCovariantDerivativeL d (C i) (Ch i) y a := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hD : directionalFDeriv a (fun x => ∑ i : I,(C i x).comp J) y=
      ∑ i : I,directionalFDeriv a (fun x => (C i x).comp J) y := by
    have hCi (i : I) : ContDiffAt ℝ ∞ (fun x => (C i x).comp J) y :=
      (hC i).clm_comp contDiffAt_const
    have hh : HasFDerivAt (fun x => ∑ i : I,(C i x).comp J)
        (∑ i : I,fderiv ℝ (fun x => (C i x).comp J) y) y :=
      HasFDerivAt.fun_sum (fun i _ => ((hCi i).differentiableAt (by simp)).hasFDerivAt)
    simpa only [directionalFDeriv,_root_.sum_apply] using DFunLike.congr_fun hh.fderiv a
  have hSum : (fun x => (∑ i : I,C i x).comp J)=(fun x => ∑ i : I,(C i x).comp J) := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply]
  unfold halfOperatorCovariantDerivativeL
  rw [hSum,hD]
  apply ContinuousLinearMap.ext
  intro u
  simp only [J,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,_root_.sum_apply,map_sum,
    Fin.sum_univ_three,map_add]
  abel
end ShrinkingSpheres
