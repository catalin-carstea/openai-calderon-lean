import Proof.HalfCovariantScalarProduct
import Proof.FrameErrorMatrixRaisingCross
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma halfOperatorCovariantDerivativeL_congr_germ (d : Data)
    (C F : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hCF : C =ᶠ[𝓝 y] F) :
    halfOperatorCovariantDerivativeL d C Ch y a=halfOperatorCovariantDerivativeL d F Ch y a := by
  have hComp : (fun x => (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) =ᶠ[𝓝 y]
      (fun x => (F x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) := by
    filter_upwards [hCF] with x hx
    rw [hx]
  unfold halfOperatorCovariantDerivativeL directionalFDeriv
  rw [hComp.fderiv_eq,hCF.eq_of_nhds]

lemma half_weighted_combination_balanced
    (c : I → ℝ)
    (Lo : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hPair : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Hi i)=
      (Lo i).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (∑ i : I,c i • Hi i)=
      (∑ i : I,c i • Lo i).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun v => c i • v) (DFunLike.congr_fun (hPair i) u))

/-- A finite weighted family retains the precise two coefficient weights
    needed by the covariant physical Green bound. -/
theorem half_weighted_combination_bounds (d : Data) (w : I → X → ℝ)
    (Lo : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hwS : ∀ i,ContDiffAt ℝ ∞ (w i) y) (hLS : ∀ i,ContDiffAt ℝ ∞ (Lo i) y)
    {B Q eps β : ℝ} (hB : 0 ≤ B) (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hβ : 0 < β)
    (hw : ∀ i,|w i y| ≤ B) (hdw : ∀ i,|directionalFDeriv a (w i) y| ≤ B*β)
    (hLo : ∀ i,‖Lo i y‖ ≤ Q*eps/β) (hHi : ∀ i,‖Hi i y‖ ≤ Q*eps/β)
    (hD : ∀ i,‖halfOperatorCovariantDerivativeL d (Lo i) (Hi i) y a‖ ≤ Q*eps) :
    ‖∑ i : I,w i y • Lo i y‖ ≤ (6*B*Q)*eps/β ∧
    ‖∑ i : I,w i y • Hi i y‖ ≤ (6*B*Q)*eps/β ∧
    ‖halfOperatorCovariantDerivativeL d (fun x => ∑ i : I,w i x • Lo i x)
      (fun x => ∑ i : I,w i x • Hi i x) y a‖ ≤ (6*B*Q)*eps := by
  have hN : 0 ≤ 3*B*(Q*eps/β) := by positivity
  have hCommon : 3*B*(Q*eps/β) ≤ (6*B*Q)*eps/β := by
    have hh := div_nonneg (mul_nonneg (mul_nonneg hB hQ) heps) hβ.le
    calc
      _ = 3*(B*Q*eps/β) := by ring
      _ ≤ 6*(B*Q*eps/β) := by linarith only [hh]
      _ = _ := by ring
  refine ⟨(norm_weighted_sum_three_le (fun i => w i y) (fun i => Lo i y) B (Q*eps/β) hB hw hLo).trans hCommon,
    (norm_weighted_sum_three_le (fun i => w i y) (fun i => Hi i y) B (Q*eps/β) hB hw hHi).trans hCommon,?_⟩
  rw [halfOperatorCovariantDerivativeL_sum_three d (fun i x => w i x • Lo i x)
    (fun i x => w i x • Hi i x) y a (fun i => (hwS i).smul (hLS i))]
  calc
    _ ≤ ∑ i : I,‖halfOperatorCovariantDerivativeL d (fun x => w i x • Lo i x)
        (fun x => w i x • Hi i x) y a‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I,(2*B*Q)*eps := Finset.sum_le_sum (fun i _ =>
      norm_halfOperatorCovariantDerivativeL_smul_le d (w i) (Lo i) (Hi i) y a
        (hwS i) (hLS i) hB hQ heps hβ (hw i) (hdw i) (hLo i) (hD i))
    _ = _ := by simp only [Fin.sum_univ_three];ring
end ShrinkingSpheres
