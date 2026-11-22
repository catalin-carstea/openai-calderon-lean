module

public import Proof.CalderonN.NormalCoefficientVelocityJets

import Proof.CalderonN.CurveAffineError
import Proof.CalderonN.SecondDerivativeCompositionBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

public section

noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Remainder after the exact center value and affine term of the actual
normalized first-metric coefficient on the radius-rescaled ball. -/
@[expose] def normalizedFirstCoefficientRemainder (d : Data dim) (y z : X dim) : Mat dim :=
  firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z) -
    ((1+d.radius y * firstDensityCenterLinear d y z) • (1 : Mat dim))

/-- The quadratic coefficient error controls its own first two spatial
derivatives on every fixed enlarged ball. All bounds precede the choice of
the admissible datum. -/
theorem uniform_normalized_coefficient_remainder_C2 (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η Q : ℝ, 0 < η ∧ 0 ≤ Q ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ z ∈ closedBall (0 : X dim) L,
      let R := normalizedFirstCoefficientRemainder d y
      ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ Q*(d.radius y)^2 ∧
        ‖fderiv ℝ R z‖ ≤ Q*(d.radius y)^2 ∧
        ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ Q*(d.radius y)^2 ∧
        (firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z)).PosDef := by
  obtain ⟨η,hη,hNormal⟩ := uniform_normal_control_on_disk (Y := Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨B,hB,hJet⟩ := exists_normalVelocityCoefficient_second_jet_bound (Y := Y) hΩ hm K ρ c₀ M Cj hK
  let Q := B*K^2*(L^2+L+1)
  have hK' : 0 < K := zero_lt_one.trans_le hK
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨η,Q,hη,hQ,?_⟩
  intro floor hfloor ε hε hεη d hd y hy z hz
  let C := firstNormalVelocityCoefficient d y
  let E := frameVectorLinear d.frame y
  let r := d.radius y
  let V := r • E
  let v := V z
  let ell := firstDensityCenterLinear d y
  let lin : X dim →L[ℝ] Mat dim := ell.smulRight (1 : Mat dim)
  let A : X dim → Mat dim := fun w => 1 + (r • lin) w
  let R := normalizedFirstCoefficientRemainder d y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hEn := hd.1.1.norm_frameVectorLinear_le hK (hd.2.1.center_mem hy) d.frame hFrame
  have hVn : ‖V‖ ≤ r*K := by
    rw [show V = r • E from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hEn hr.le
  have hzL : ‖z‖ ≤ L := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hv : ‖v‖ ≤ r*K*L :=
    (V.le_opNorm z).trans (mul_le_mul hVn hzL (norm_nonneg _) (by positivity))
  have hPack (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ C (t • v) ∧
        ‖fderiv ℝ (fderiv ℝ C) (t • v)‖ ≤ B ∧ (C (t • v)).PosDef := by
    have htz : t • z ∈ closedBall (0 : X dim) L := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans hzL
    have hFrameDisk := frameVector_mem_disk d.γ d.frame y (t • z) L hFrame htz
    have hh := hNormal floor hfloor ε hε hεη d hd y hy _ hFrameDisk
    have hEq : r • frameVector d.frame y (t • z) = t • v := by
      rw [← frameVectorLinear_apply,map_smul,smul_comm]
      rfl
    rw [hEq] at hh
    exact hJet floor ε d hd y hy _ hh.1.1 hh.1.2 hh.2.2.2.1
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl,zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hC₀ : ContDiffAt ℝ ∞ C 0 := by simpa only [zero_smul] using (hPack 0 h0).1
  have hCv : ContDiffAt ℝ ∞ C v := by simpa only [one_smul] using (hPack 1 h1).1
  have hCenter : C 0 = 1 := by
    ext i j
    have hEq := firstNormalVelocityCoefficient_rescaled d y 0 0 i j
    rw [zero_smul,hd.normalizedFirstNormalCoeff_center hn hK' hy] at hEq
    exact hEq
  have hFirst : (fderiv ℝ C 0).comp E = lin := by
    ext w i j
    let a := E w
    have hs : HasDerivAt (fun t : ℝ => t • a) a 0 := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const a
    have hCD : HasFDerivAt C (fderiv ℝ C 0) ((0 : ℝ) • a) := by
      simpa only [zero_smul] using (hC₀.differentiableAt (by simp)).hasFDerivAt
    have hD := hCD.comp_hasDerivAt 0 hs
    have hDE := (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt 0 hD
    have hExact := hd.normalizedFirstNormalCoeff_first hn hΩ hK' hy w i j
    have hEq : (matrixEntryL i j ∘ fun t : ℝ => C (t • a)) =
        (fun t : ℝ => normalizedFirstNormalCoeff d y t w i j) :=
      funext fun t => by simpa only [Function.comp_apply,matrixEntryL_apply,C,a,E,frameVectorLinear_apply]
        using firstNormalVelocityCoefficient_rescaled d y w t i j
    change HasDerivAt (matrixEntryL i j ∘ fun t : ℝ => C (t • a))
      (matrixEntryL i j (fderiv ℝ C 0 a)) 0 at hDE
    rw [hEq] at hDE
    have hVal := hDE.unique hExact
    simpa only [matrixEntryL_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      Matrix.smul_apply,smul_eq_mul,a,ell,lin] using hVal
  have hA : ContDiff ℝ ∞ A := contDiff_const.add (r • lin).contDiff
  have hA₁ : fderiv ℝ A = fun _ => r • lin := by
    funext w
    change fderiv ℝ (fun x => 1 + (r • lin) x) w = _
    exact ((r • lin).hasFDerivAt.const_add 1).fderiv
  have hR : R = C ∘ V - A := by
    funext w
    simp only [R,normalizedFirstCoefficientRemainder,C,V,E,smul_apply,frameVectorLinear_apply,
      Pi.sub_apply,Function.comp_apply,A,lin,ell,r,ContinuousLinearMap.smulRight_apply,add_smul,
      smul_smul,one_smul]
  have hRsm : ContDiffAt ℝ ∞ R z := by
    rw [hR]
    exact (hCv.comp z V.contDiff.contDiffAt).sub hA.contDiffAt
  let D := fderiv ℝ C
  have hDT (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => D (u • v)) (fderiv ℝ D (t • v) v) t := by
    have hs : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id t).smul_const v
    exact ((((hPack t ht).1.fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t hs)
  have hDerror (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖D (t • v) - D 0‖ ≤ (B*‖v‖)*t := by
    have he := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hDT s hs).differentiableAt) (fun s hs => by
        rw [(hDT s hs).deriv]
        exact ((fderiv ℝ D (s • v)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hPack s hs).2.1 (norm_nonneg v))) h0 ht
    simpa only [zero_smul,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using he
  have hValue : ‖C v-C 0-D 0 v‖ ≤ B*‖v‖^2 := by
    let G (t : ℝ) := C (t • v)
    let F (t : ℝ) := D (t • v) v
    have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt G (F t) t := by
      have hs : HasDerivAt (fun t : ℝ => t • v) v t := by
        simpa only [id_eq,one_smul] using (hasDerivAt_id t).smul_const v
      exact ((hPack t ht).1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hs
    have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖F t - D 0 v‖ ≤ (B*‖v‖^2)*t := by
      change ‖(D (t • v) - D 0) v‖ ≤ _
      exact ((D (t • v) - D 0).le_opNorm v).trans
        ((mul_le_mul_of_nonneg_right (hDerror t ht) (norm_nonneg v)).trans_eq (by ring))
    simpa only [G,one_smul,one_pow,mul_one] using norm_curve_affine_error_le
      G F (C 0) (D 0 v) (B*‖v‖^2) 1 (by positivity) h1 hG (by simp [G]) hF
  have hR₀ : R z = C v-C 0-D 0 v := by
    have h := congrArg (fun T : X dim →L[ℝ] Mat dim => T z) hFirst
    rw [hR,hCenter]
    change C v - (1 + (r • lin) z) = C v - 1 - D 0 v
    have he : D 0 v = (r • lin) z := by
      have hh : fderiv ℝ C 0 (E z) = lin z := h
      simp only [D,v,V,smul_apply,map_smul,hh]
    rw [he]
    abel
  have hComp : fderiv ℝ (C ∘ V) z = (D v).comp V :=
    ((hCv.differentiableAt (by simp)).hasFDerivAt.comp z V.hasFDerivAt).fderiv
  have hR₁ : fderiv ℝ R z = (D v-D 0).comp V := by
    rw [hR,fderiv_sub ((hCv.comp z V.contDiff.contDiffAt).differentiableAt (by simp))
      (hA.differentiable (by simp) z),hComp,hA₁,ContinuousLinearMap.sub_comp]
    have h : (D 0).comp V = r • lin := by
      change (fderiv ℝ C 0).comp (r • E) = r • lin
      rw [ContinuousLinearMap.comp_smul,hFirst]
    rw [h]
  have hR₂ : fderiv ℝ (fderiv ℝ R) z = fderiv ℝ (fderiv ℝ (C ∘ V)) z := by
    have hh : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (C ∘ V) w := by
      filter_upwards [((hCv.comp z V.contDiff.contDiffAt).of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)]
        with w hw using hw.differentiableAt (by simp)
    have he : fderiv ℝ R =ᶠ[𝓝 z] (fun w => fderiv ℝ (C ∘ V) w-r • lin) := by
      filter_upwards [hh] with w hw
      rw [hR,fderiv_sub hw (hA.differentiable (by simp) w),hA₁]
    rw [he.fderiv_eq,fderiv_sub_const]
  change ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ Q*r^2 ∧
    ‖fderiv ℝ R z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ (fderiv ℝ R) z‖ ≤ Q*r^2 ∧
    (firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)).PosDef
  have hpos : (firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)).PosDef := by
    simpa only [v,V,E,smul_apply,frameVectorLinear_apply,C,one_smul] using (hPack 1 h1).2.2
  refine ⟨hRsm,?_,?_,?_,hpos⟩
  · rw [hR₀]
    refine hValue.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) hB).trans ?_)
    have hb := mul_le_mul_of_nonneg_left (show L^2 ≤ L^2+L+1 by linarith) (show 0 ≤ B*K^2*r^2 by positivity)
    dsimp only [Q,r] at *
    nlinarith only [hb]
  · rw [hR₁]
    have hD := hDerror 1 h1
    simp only [one_smul,mul_one] at hD
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hD.trans (mul_le_mul_of_nonneg_left hv hB)) hVn (norm_nonneg _) (by positivity)).trans ?_)
    have hb := mul_le_mul_of_nonneg_left (show L ≤ L^2+L+1 by nlinarith [sq_nonneg L])
      (show 0 ≤ B*K^2*r^2 by positivity)
    dsimp only [Q,r] at *
    nlinarith only [hb]
  · rw [hR₂]
    have h := norm_second_fderiv_comp_at V C z V.contDiff.contDiffAt hCv
    have he : fderiv ℝ (⇑V) = fun _ => V := funext fun _ => V.fderiv
    simp only [he,fderiv_fun_const,Pi.zero_apply,norm_zero,mul_zero,zero_add] at h
    refine h.trans ((mul_le_mul (by simpa only [v,one_smul] using (hPack 1 h1).2.1)
      (pow_le_pow_left₀ (norm_nonneg _) hVn 2) (sq_nonneg _) hB).trans ?_)
    have hb := mul_le_mul_of_nonneg_left (show 1 ≤ L^2+L+1 by nlinarith [sq_nonneg L])
      (show 0 ≤ B*K^2*r^2 by positivity)
    dsimp only [Q,r] at *
    nlinarith only [hb]

end CalderonN
