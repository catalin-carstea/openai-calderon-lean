module

public import Proof.CalderonN.CenterCoefficientAtOrigin
public import Proof.CalderonN.EnlargedNormalInverse

import Mathlib.Tactic

/-! Uniform quadratic error for horizontal variation of the normalized
coefficient on the radius-rescaled ball. The center differentiation holds
the physical radius fixed. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def scaledCenterCoefficientDerivative (d : Data dim) (y a z : X dim) : Mat dim :=
  actualCenterNormalCoefficientDerivative d y a (d.radius y • z)

@[expose] def actualCenterCoefficientRemainder (d : Data dim) (y a z : X dim) : Mat dim :=
  scaledCenterCoefficientDerivative d y a z -
    (d.radius y*centerDensityCovariantLinear d y a z) • (1 : Mat dim)

theorem uniform_actual_center_coefficient_jet (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η Q : ℝ, 0 < η ∧ 0 ≤ Q ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ a : X dim, ‖a‖ ≤ K →
      ‖centerDensityCovariantLinear d y a‖ ≤ Q ∧ ∀ z ∈ closedBall (0 : X dim) L,
      let R := actualCenterCoefficientRemainder d y a
      ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ Q*(d.radius y)^2 ∧
        ‖fderiv ℝ R z‖ ≤ Q*(d.radius y)^2 := by
  obtain ⟨η₀,hη₀,hNear⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨B,hB,hJet⟩ := exists_actualCenterCoefficientFamily_jet_bound dim hm K M hK
  have hK' : 0 < K := zero_lt_one.trans_le hK
  let η := min η₀ (min (1/(L+1)) (ρ/(2*(L+1))))
  let Q := B*(1+L^2+L)
  refine ⟨η,Q,lt_min hη₀ (lt_min (by positivity) (by positivity)),by positivity,?_⟩
  intro floor hfloor ε hε hεη d hd y hy a ha
  let r := d.radius y
  let U := frameVectorLinear d.frame y
  let C := actualCenterNormalCoefficientDerivative d y a
  let A := (centerDensityCovariantLinear d y a).smulRight (1 : Mat dim)
  let R := actualCenterCoefficientRemainder d y a
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hre : r ≤ ε :=
    (le_mul_of_one_le_right hr.le (one_le_pow₀ (hfloor.trans ((hd.2.2.2.2.1.2 y hy).2.1)))).trans
      (hd.2.2.2.2.2 y hy).2
  have hε₁ : ε*(L+1) ≤ 1 :=
    (le_div_iff₀ (show 0 < L+1 by positivity)).mp
      (hεη.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hερ : ε*(2*(L+1)) ≤ ρ :=
    (le_div_iff₀ (show 0 < 2*(L+1) by positivity)).mp
      (hεη.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrL₁ : r*L ≤ 1 :=
    ((mul_le_mul_of_nonneg_right hre hL).trans
      (mul_le_mul_of_nonneg_left (by linarith : L ≤ L+1) hε)).trans hε₁
  have hrLρ : r*L < ρ := by
    have h := (mul_le_mul_of_nonneg_right hre hL).trans
      (mul_le_mul_of_nonneg_left (by linarith : L ≤ L+1) hε)
    linarith only [h,hερ,hρ]
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  obtain ⟨hC₀,hC₁⟩ := actualCenterNormalCoefficientDerivative_center_jet hn hY hΩ hd hK' hρ hy a
  have hA : fderiv ℝ C 0 = A := hC₁
  have hZero : C 0 = 0 := hC₀
  have hEll : ‖centerDensityCovariantLinear d y a‖ ≤ Q := by
    have hvel : r • (0 : X dim) ∈ disk d.γ y L := by
      rw [smul_zero]
      exact zero_mem_disk d.γ y L
    have hb := hNear floor hfloor ε hε (hεη.trans (min_le_left _ _)) d hd y hy _ hvel
    have hnear : ‖normalVerticalJacobian d.expMap y (U 0)-
        ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2 : ℝ) := by
      simpa only [map_zero,smul_zero] using hb.2.2.2.1
    have hstrict : metricPair d.γ y (U 0) (U 0) < (max ρ r)^2 := by
      rw [map_zero,show metricPair d.γ y 0 0 = 0 from by simp [metricPair]]
      exact sq_pos_of_pos (hρ.trans_le (le_max_left _ _))
    obtain ⟨hF,hFb⟩ := hJet hY hΩ hd y hy a 0 ha (by simp) (by simp) hstrict hnear
    have hD := centerDerivativeSlice_first_bound _ _ hF hB (hFb 2 (by omega))
    change ‖fderiv ℝ C 0‖ ≤ B at hD
    rw [hA] at hD
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    have hh := (A.le_opNorm w).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
    rw [show A w = centerDensityCovariantLinear d y a w • (1 : Mat dim) from rfl,
      norm_smul,norm_one,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by
      dsimp [Q]
      nlinarith only [mul_nonneg hB (sq_nonneg L),mul_nonneg hB hL]) (norm_nonneg _))
  refine ⟨hEll,?_⟩
  intro z hz
  let V := r • ContinuousLinearMap.id ℝ (X dim)
  let v := V z
  have hzL : ‖z‖ ≤ L := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hVn : ‖V‖ ≤ r := by
    rw [show V = r • ContinuousLinearMap.id ℝ (X dim) from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hr.le).trans_eq (mul_one _)
  have hv : ‖v‖ ≤ r*L :=
    (V.le_opNorm z).trans (mul_le_mul hVn hzL (norm_nonneg _) hr.le)
  have hPack (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ C (t • v) ∧ ‖fderiv ℝ (fderiv ℝ C) (t • v)‖ ≤ B := by
    have htz : t • z ∈ closedBall (0 : X dim) L := by
      rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans hzL
    have htW := frameVector_mem_disk d.γ d.frame y (t • z) L hFrame htz
    have hh := hNear floor hfloor ε hε (hεη.trans (min_le_left _ _)) d hd y hy _ htW
    have hEq : U (t • v) = r • frameVector d.frame y (t • z) := by
      change U (t • (r • z)) = _
      rw [smul_comm t r,map_smul,frameVectorLinear_apply]
    have hstrict : metricPair d.γ y (U (t • v)) (U (t • v)) < (max ρ r)^2 := by
      rw [hEq,metricPair_smul_left,metricPair_smul_right]
      have hw' := mul_le_mul_of_nonneg_left (show
        metricPair d.γ y (frameVector d.frame y (t • z)) (frameVector d.frame y (t • z)) ≤ L^2
        from htW) (sq_nonneg r)
      have hmR : 0 ≤ max ρ r := hρ.le.trans (le_max_left _ _)
      have hS : (r*L)^2 < (max ρ r)^2 :=
        (sq_lt_sq₀ (mul_nonneg hr.le hL) hmR).2 (hrLρ.trans_le (le_max_left _ _))
      nlinarith only [hS,hw']
    have hvn : ‖t • v‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans (hv.trans hrL₁)
    obtain ⟨hF,hFb⟩ := hJet hY hΩ hd y hy a (t • v) ha hvn
      (by rw [hEq]; exact hh.1.2) hstrict (by rw [hEq]; exact hh.2.2.2.1)
    exact centerDerivativeSlice_smooth_second_bound _ _ hF hB (hFb 3 le_rfl)
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hCv : ContDiffAt ℝ ∞ C v := by simpa only [one_smul] using (hPack 1 h1).1
  have hR : R = C ∘ V - (r • A : X dim →L[ℝ] Mat dim) := by
    funext w
    simp only [R,actualCenterCoefficientRemainder,scaledCenterCoefficientDerivative,
      Pi.sub_apply,Function.comp_apply,smul_apply,V,ContinuousLinearMap.id_apply,C,
      A,ContinuousLinearMap.smulRight_apply,smul_smul,r]
  have hCV : ContDiffAt ℝ ∞ (C ∘ V) z := hCv.comp z V.contDiff.contDiffAt
  have hRsm : ContDiffAt ℝ ∞ R z := by
    rw [hR]
    exact hCV.sub (r • A).contDiff.contDiffAt
  have hR₀ : R z = C v-C 0-fderiv ℝ C 0 v := by
    rw [hR,hZero,sub_zero,hA]
    change C v-(r • A) z = C v-A (r • z)
    rw [map_smul,smul_apply]
  have hR₁ : fderiv ℝ R z = (fderiv ℝ C v-fderiv ℝ C 0).comp V := by
    rw [hR,fderiv_sub (hCV.differentiableAt (by simp)) (r • A).differentiableAt,
      ((hCv.differentiableAt (by simp)).hasFDerivAt.comp z V.hasFDerivAt).fderiv,
      (r • A).fderiv,ContinuousLinearMap.sub_comp,hA]
    have hLin : A.comp V = r • A := by
      ext1 w
      change A (r • w) = r • A w
      exact map_smul A r w
    rw [hLin]
  have h := norm_taylor_remainder_of_second_bound C v hB hPack
  change ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ R z‖ ≤ Q*r^2
  refine ⟨hRsm,?_,?_⟩
  · rw [hR₀]
    refine h.1.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) hB).trans ?_)
    dsimp [Q]
    have hn : 0 ≤ B*L*r^2 := by positivity
    nlinarith only [hn,show 0 ≤ B*r^2 by positivity]
  · rw [hR₁]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (h.2.trans (mul_le_mul_of_nonneg_left hv hB)) hVn (norm_nonneg _) (by positivity)).trans ?_)
    dsimp [Q]
    have hn : 0 ≤ B*L^2*r^2 := by positivity
    nlinarith only [hn,show 0 ≤ B*r^2 by positivity]

end CalderonN
