import Proof.CurveAffineError
import Proof.LocalFlowVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The genuine second derivative controls an affine vertical Taylor
    remainder and the difference of first vertical derivatives. -/
theorem vertical_affine_jet_taylor (F : P × Q → E) (y : P) (v : Q)
    (hSmooth : ∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ ∞ F (y,t • v))
    (C : ℝ) (hC : 0 ≤ C)
    (hSecond : ∀ t ∈ Icc (0:ℝ) 1,‖fderiv ℝ (fderiv ℝ F) (y,t • v)‖ ≤ C) :
    ‖F (y,v)-F (y,0)-fderiv ℝ F (y,0) (0,v)‖ ≤ C*‖v‖^2 ∧
    ∀ b : Q,‖fderiv ℝ F (y,v) (0,b)-fderiv ℝ F (y,0) (0,b)‖ ≤ C*‖v‖*‖b‖ := by
  let G : ℝ → E := fun t => F (y,t • v)
  let V (b : Q) (t : ℝ) := fderiv ℝ F (y,t • v) (0,b)
  have hInput (t : ℝ) : HasDerivAt (fun s : ℝ => (y,s • v)) ((0:P),v) t := by
    convert (hasDerivAt_const t y).prodMk ((hasDerivAt_id t).smul_const v) using 1 <;> simp
  have hVD (b : Q) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (V b) (fderiv ℝ (fderiv ℝ F) (y,t • v) (0,v) (0,b)) t := by
    have hD := (((hSmooth t ht).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hInput t)
    simpa only [V,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,zero_add,add_zero,Function.comp_def] using hD.clm_apply (hasDerivAt_const t ((0:P),b))
  have hBound (b : Q) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖deriv (V b) t‖ ≤ C*‖v‖*‖b‖ := by
    rw [(hVD b t ht).deriv]
    have hb := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ F) (y,t • v)) ((0:P),v) ((0:P),b)
    exact hb.trans ((show ‖fderiv ℝ (fderiv ℝ F) (y,t • v)‖*‖((0:P),v)‖*‖((0:P),b)‖ ≤
      C*‖((0:P),v)‖*‖((0:P),b)‖ by gcongr;exact hSecond t ht).trans_eq (by
        simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v),max_eq_right (norm_nonneg b)]))
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hV0 (b : Q) : V b 0 = fderiv ℝ F (y,0) (0,b) := by simp only [V,zero_smul]
  have hFirst (b : Q) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖V b t-fderiv ℝ F (y,0) (0,b)‖ ≤ (C*‖v‖*‖b‖)*t := by
    have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hVD b s hs).differentiableAt) (hBound b) hz ht
    simpa only [hV0 b,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb
  have hone : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  constructor
  · have hGD (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt G (V v t) t := by
      exact (hSmooth t ht).differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt t (hInput t)
    have hb := norm_curve_affine_error_le G (V v) (F (y,0)) (fderiv ℝ F (y,0) (0,v)) (C*‖v‖^2) 1 (by positivity) hone hGD
      (by simp only [G,zero_smul]) (fun t ht => by simpa only [sub_zero,pow_two,mul_assoc] using hFirst v t ht)
    simpa only [G,one_smul,smul_zero,sub_zero,one_pow,mul_one] using hb
  · intro b
    simpa only [V,one_smul,mul_one] using hFirst b 1 hone

/-- A vanishing vertical first jet and genuine second derivative control give
    both the quadratic value remainder and its linear vertical derivative. -/
theorem vertical_zero_jet_taylor (F : P × Q → E) (y : P) (v : Q)
    (hSmooth : ∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ ∞ F (y,t • v))
    (hZero : ∀ b : Q,fderiv ℝ F (y,0) (0,b) = 0) (C : ℝ) (hC : 0 ≤ C)
    (hSecond : ∀ t ∈ Icc (0:ℝ) 1,‖fderiv ℝ (fderiv ℝ F) (y,t • v)‖ ≤ C) :
    ‖F (y,v)-F (y,0)‖ ≤ C*‖v‖^2 ∧
    ∀ b : Q,‖fderiv ℝ F (y,v) (0,b)‖ ≤ C*‖v‖*‖b‖ := by
  have hb := vertical_affine_jet_taylor F y v hSmooth C hC hSecond
  simpa only [hZero,sub_zero] using hb

end ShrinkingSpheres
