import Proof.HalfCovariantScalarProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma halfOperatorCovariantDerivativeL_add (d : Data)
    (C F : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch Fh : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hF : ContDiffAt ℝ ∞ F y) :
    halfOperatorCovariantDerivativeL d (fun x => C x+F x) (fun x => Ch x+Fh x) y a=
      halfOperatorCovariantDerivativeL d C Ch y a+halfOperatorCovariantDerivativeL d F Fh y a := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hSum : (fun x => (C x+F x).comp J)=(fun x => (C x).comp J+(F x).comp J) := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    rfl
  have hD : directionalFDeriv a (fun x => (C x+F x).comp J) y=
      directionalFDeriv a (fun x => (C x).comp J) y+directionalFDeriv a (fun x => (F x).comp J) y := by
    rw [hSum]
    unfold directionalFDeriv
    rw [fderiv_fun_add ((hC.clm_comp contDiffAt_const).differentiableAt (by simp))
      ((hF.clm_comp contDiffAt_const).differentiableAt (by simp))]
    rfl
  unfold halfOperatorCovariantDerivativeL
  rw [hD]
  apply ContinuousLinearMap.ext
  intro u
  simp only [J,ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,map_add]
  abel

/-- A small scalar against a bounded physical family has the precise
    coefficient and literal covariant weights of the first-form estimate. -/
theorem half_small_scalar_product_bounds (d : Data) (f : X → ℝ)
    (Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hfS : ContDiffAt ℝ ∞ f y) (hLS : ContDiffAt ℝ ∞ Lo y)
    {B Q eps β : ℝ} (hB : 0 ≤ B) (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hβ : 1 ≤ β)
    (hf : |f y| ≤ B*eps/β) (hdf : |directionalFDeriv a f y| ≤ B*eps)
    (hLo : ‖Lo y‖ ≤ Q) (hHi : ‖Hi y‖ ≤ Q)
    (hD : ‖halfOperatorCovariantDerivativeL d Lo Hi y a‖ ≤ Q) :
    ‖f y • Lo y‖ ≤ (2*B*Q)*eps/β ∧ ‖f y • Hi y‖ ≤ (2*B*Q)*eps/β ∧
    ‖halfOperatorCovariantDerivativeL d (fun x => f x • Lo x) (fun x => f x • Hi x) y a‖ ≤ (2*B*Q)*eps := by
  have hβP : 0 < β := zero_lt_one.trans_le hβ
  let Bs := B*eps/β
  have hBs : 0 ≤ Bs := div_nonneg (mul_nonneg hB heps) hβP.le
  have hW : |directionalFDeriv a f y| ≤ Bs*β :=
    hdf.trans_eq (by dsimp only [Bs];field_simp <;> ring)
  have hL : ‖Lo y‖ ≤ Q*β/β := by simpa only [mul_div_cancel_right₀ Q hβP.ne'] using hLo
  have hQβ : Q ≤ Q*β := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hQ
  have hDC := norm_halfOperatorCovariantDerivativeL_smul_le d f Lo Hi y a hfS hLS hBs hQ hβP.le hβP
    hf hW hL (hD.trans hQβ)
  have hCommon : (B*eps/β)*Q ≤ (2*B*Q)*eps/β := by
    have hh : 0 ≤ B*Q*eps/β := div_nonneg (mul_nonneg (mul_nonneg hB hQ) heps) hβP.le
    calc
      _ = B*Q*eps/β := by ring
      _ ≤ 2*(B*Q*eps/β) := by linarith only [hh]
      _ = _ := by ring
  refine ⟨?_,?_,hDC.trans_eq ?_⟩
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hf hLo (norm_nonneg _) hBs).trans hCommon
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hf hHi (norm_nonneg _) hBs).trans hCommon
  · dsimp only [Bs]
    field_simp <;> ring
end ShrinkingSpheres
