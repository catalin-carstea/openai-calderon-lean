import Proof.CurveAffineError
import Proof.LocalFlowVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma center_fderiv_zero_of_zero_slice (F : P × Q → E) (y a : P)
    (hF : ContDiffAt ℝ ∞ F (y,0))
    (hZero : (fun x : P => F (x,0)) =ᶠ[𝓝 y] (fun _ => 0)) :
    fderiv ℝ F (y,0) (a,0) = 0 := by
  have hInput : HasFDerivAt (fun x : P => (x,(0:Q))) (ContinuousLinearMap.inl ℝ P Q) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const (0:Q) y)
  have hComp := (hF.differentiableAt (by simp)).hasFDerivAt.comp y hInput
  simp only [Function.comp_def] at hComp
  have hEq := congrArg (fun L : P →L[ℝ] E => L a) hZero.fderiv_eq
  rw [hComp.fderiv] at hEq
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,fderiv_const_apply,zero_apply] using hEq

lemma center_velocity_second_fderiv_eq_of_slice (F : P × Q → E) (y a : P) (b : Q) (q : P → E)
    (hF : ContDiffAt ℝ ∞ F (y,0))
    (hZero : (fun x : P => fderiv ℝ F (x,0) (0,b)) =ᶠ[𝓝 y] q) :
    fderiv ℝ (fderiv ℝ F) (y,0) (0,b) (a,0) = fderiv ℝ q y a := by
  have hInput : HasFDerivAt (fun x : P => (x,(0:Q))) (ContinuousLinearMap.inl ℝ P Q) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const (0:Q) y)
  have hDF := ((hF.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp y hInput
  have hEval := hDF.clm_apply (hasFDerivAt_const ((0:P),b) y)
  have hEq := congrArg (fun L : P →L[ℝ] E => L a) hZero.fderiv_eq
  simp only [Function.comp_def] at hEval
  rw [hEval.fderiv] at hEq
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.inl_apply,zero_apply,map_zero,zero_add] at hEq
  exact ((hF.isSymmSndFDerivAt (by simp)).eq (0,b) (a,0)).trans hEq

lemma center_velocity_second_fderiv_zero (F : P × Q → E) (y a : P) (b : Q)
    (hF : ContDiffAt ℝ ∞ F (y,0))
    (hZero : (fun x : P => fderiv ℝ F (x,0) (0,b)) =ᶠ[𝓝 y] (fun _ => 0)) :
    fderiv ℝ (fderiv ℝ F) (y,0) (0,b) (a,0) = 0 := by
  have hb := center_velocity_second_fderiv_eq_of_slice F y a b (fun _ => 0) hF hZero
  simpa only [fderiv_const_apply,zero_apply] using hb

/-- The full affine center Taylor remainder is quadratic, using only
    third joint jets. This common derivation also covers nonzero first radial models. -/
theorem norm_center_fderiv_affine_error_of_third_bound (F : P × Q → E) (y a : P) (v : Q)
    (hSmooth : ∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ ∞ F (y,t • v))
    (C : ℝ) (hC : 0 ≤ C)
    (hThird : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)‖ ≤ C) :
    ‖fderiv ℝ F (y,v) (a,0)-fderiv ℝ F (y,0) (a,0)-
      fderiv ℝ (fderiv ℝ F) (y,0) (0,v) (a,0)‖ ≤ C*‖v‖^2*‖a‖ := by
  let G : ℝ → E := fun t => fderiv ℝ F (y,t • v) (a,0)
  let V : ℝ → E := fun t => fderiv ℝ (fderiv ℝ F) (y,t • v) (0,v) (a,0)
  let B := C*‖v‖^2*‖a‖
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hInput (t : ℝ) : HasDerivAt (fun s : ℝ => (y,s • v)) ((0:P),v) t := by
    convert (hasDerivAt_const t y).prodMk ((hasDerivAt_id t).smul_const v) using 1 <;> simp
  have hGD (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt G (V t) t := by
    have hD := (((hSmooth t ht).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hInput t)
    simpa only [G,V,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,zero_add,add_zero,Function.comp_def] using hD.clm_apply (hasDerivAt_const t ((a,(0:Q))))
  have hVD (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt V (fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v) (0,v) (0,v) (a,0)) t := by
    have hD := ((((hSmooth t ht).fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hInput t)
    simpa only [V,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,zero_add,add_zero,Function.comp_def] using (hD.clm_apply (hasDerivAt_const t ((0:P),v))).clm_apply (hasDerivAt_const t ((a,(0:Q))))
  have hBound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖deriv V t‖ ≤ B := by
    rw [(hVD t ht).deriv]
    let T := fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)
    have hb : ‖T (0,v) (0,v) (a,0)‖ ≤ ‖T‖*‖((0:P),v)‖*‖((0:P),v)‖*‖(a,(0:Q))‖ :=
      (ContinuousLinearMap.le_opNorm₂ (T (0,v)) (0,v) (a,0)).trans (by gcongr;exact T.le_opNorm (0,v))
    exact hb.trans ((show ‖T‖*‖((0:P),v)‖*‖((0:P),v)‖*‖(a,(0:Q))‖ ≤
      C*‖((0:P),v)‖*‖((0:P),v)‖*‖(a,(0:Q))‖ by gcongr;exact hThird t ht).trans_eq (by
        dsimp only [B];simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v),max_eq_left (norm_nonneg a)];ring))
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hG0 : G 0 = fderiv ℝ F (y,0) (a,0) := by simp only [G,zero_smul]
  have hV0 : V 0 = fderiv ℝ (fderiv ℝ F) (y,0) (0,v) (a,0) := by simp only [V,zero_smul]
  have hError (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖V t-fderiv ℝ (fderiv ℝ F) (y,0) (0,v) (a,0)‖ ≤ B*t := by
    have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hVD s hs).differentiableAt) hBound hz ht
    simpa only [hV0,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb
  have hb := norm_curve_affine_error_le G V (fderiv ℝ F (y,0) (a,0)) (fderiv ℝ (fderiv ℝ F) (y,0) (0,v) (a,0)) B 1 hB (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩) hGD hG0 hError
  simpa only [G,one_smul,one_pow,mul_one,B] using hb

/-- Vanishing of the first vertical jet at zero velocity is preserved
    by center differentiation, giving a quadratic center derivative difference. -/
theorem norm_center_fderiv_sub_zero_quadratic_of_third_bound (F : P × Q → E) (y a : P) (v : Q)
    (hSmooth : ∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ ∞ F (y,t • v))
    (hVertical : (fun x : P => fderiv ℝ F (x,0) (0,v)) =ᶠ[𝓝 y] (fun _ => 0))
    (C : ℝ) (hC : 0 ≤ C)
    (hThird : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)‖ ≤ C) :
    ‖fderiv ℝ F (y,v) (a,0)-fderiv ℝ F (y,0) (a,0)‖ ≤ C*‖v‖^2*‖a‖ := by
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hF0 : ContDiffAt ℝ ∞ F (y,0) := by simpa only [zero_smul] using hSmooth 0 hz
  have hZero := center_velocity_second_fderiv_zero F y a v hF0 hVertical
  have hb := norm_center_fderiv_affine_error_of_third_bound F y a v hSmooth C hC hThird
  simpa only [hZero,sub_zero] using hb

/-- The mixed vertical-center derivative changes linearly along the velocity segment. -/
theorem norm_center_velocity_second_fderiv_sub_zero_of_third_bound (F : P × Q → E) (y a : P) (v b : Q)
    (hSmooth : ∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ ∞ F (y,t • v))
    (C : ℝ) (hC : 0 ≤ C)
    (hThird : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)‖ ≤ C) :
    ‖fderiv ℝ (fderiv ℝ F) (y,v) (0,b) (a,0)-fderiv ℝ (fderiv ℝ F) (y,0) (0,b) (a,0)‖ ≤ C*‖v‖*‖b‖*‖a‖ := by
  let V : ℝ → E := fun t => fderiv ℝ (fderiv ℝ F) (y,t • v) (0,b) (a,0)
  let B := C*‖v‖*‖b‖*‖a‖
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hInput (t : ℝ) : HasDerivAt (fun s : ℝ => (y,s • v)) ((0:P),v) t := by
    convert (hasDerivAt_const t y).prodMk ((hasDerivAt_id t).smul_const v) using 1 <;> simp
  have hVD (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt V (fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v) (0,v) (0,b) (a,0)) t := by
    have hD := ((((hSmooth t ht).fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hInput t)
    simpa only [V,_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      zero_apply,map_zero,zero_add,add_zero,Function.comp_def] using
      (hD.clm_apply (hasDerivAt_const t ((0:P),b))).clm_apply (hasDerivAt_const t ((a,(0:Q))))
  have hBound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖deriv V t‖ ≤ B := by
    rw [(hVD t ht).deriv]
    let T := fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)
    have hb : ‖T (0,v) (0,b) (a,0)‖ ≤ ‖T‖*‖((0:P),v)‖*‖((0:P),b)‖*‖(a,(0:Q))‖ :=
      (ContinuousLinearMap.le_opNorm₂ (T (0,v)) (0,b) (a,0)).trans (by gcongr;exact T.le_opNorm (0,v))
    exact hb.trans ((show ‖T‖*‖((0:P),v)‖*‖((0:P),b)‖*‖(a,(0:Q))‖ ≤
      C*‖((0:P),v)‖*‖((0:P),b)‖*‖(a,(0:Q))‖ by gcongr;exact hThird t ht).trans_eq (by
        dsimp only [B];simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v),
          max_eq_right (norm_nonneg b),max_eq_left (norm_nonneg a)]))
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hV0 : V 0 = fderiv ℝ (fderiv ℝ F) (y,0) (0,b) (a,0) := by simp only [V,zero_smul]
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hVD s hs).differentiableAt) hBound hz (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  simpa only [V,hV0,one_smul,sub_zero,Real.norm_eq_abs,abs_one,mul_one,B] using hb

/-- The angular jet of the center remainder gains one velocity factor. -/
theorem norm_center_velocity_second_fderiv_of_third_bound (F : P × Q → E) (y a : P) (v b : Q)
    (hSmooth : ∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ ∞ F (y,t • v))
    (hVertical : (fun x : P => fderiv ℝ F (x,0) (0,b)) =ᶠ[𝓝 y] (fun _ => 0))
    (C : ℝ) (hC : 0 ≤ C)
    (hThird : ∀ t ∈ Icc (0:ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ F)) (y,t • v)‖ ≤ C) :
    ‖fderiv ℝ (fderiv ℝ F) (y,v) (0,b) (a,0)‖ ≤ C*‖v‖*‖b‖*‖a‖ := by
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have hF0 : ContDiffAt ℝ ∞ F (y,0) := by simpa only [zero_smul] using hSmooth 0 hz
  have hZero := center_velocity_second_fderiv_zero F y a b hF0 hVertical
  have hb := norm_center_velocity_second_fderiv_sub_zero_of_third_bound F y a v b hSmooth C hC hThird
  simpa only [hZero,sub_zero] using hb

end ShrinkingSpheres
