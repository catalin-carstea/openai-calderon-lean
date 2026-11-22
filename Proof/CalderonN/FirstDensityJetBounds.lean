module

public import Proof.CalderonN.FirstMetricNormalJets

import Proof.CalderonN.ExpJetBounds
import Proof.CalderonN.FramedNormalMetric
import Proof.CalderonN.FirstMetricConformalDepth
import Mathlib.Tactic

/-! The conformal density estimates from Proposition 5.3 with the
dimension-dependent exponent in the geometric transformation law. -/

public section
set_option maxSynthPendingDepth 16

noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- First angular derivative of the unnormalized scalar density at the center. -/
@[expose] def firstDensityCenterDerivative (d : Data dim) (y : X dim) : X dim →L[ℝ] ℝ :=
  (fderiv ℝ (firstMetricDensityFactor d.γ d.g₁) y).comp (frameVectorLinear d.frame y)

theorem Background.firstMetricDensityFactor_le {Ω : Set (X dim)} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField dim} {e : Frame dim}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X dim} (hx : x ∈ Ω) :
    firstMetricDensityFactor γ g₁ x ≤ K^(dim-2) := by
  have h11 := ((hB.2.1.2 x hx).2 (axis (0 : I dim))).2
  have h00 : metricPair g₁ x (axis (0 : I dim)) (axis (0 : I dim)) = g₁ x 0 0 := by
    simp [metricPair,axis]
  rw [h00,norm_axis,one_pow,mul_one] at h11
  have hc : (firstMetricScale γ g₁ x)^2 ≤ K^2 := by
    rw [hB.firstMetricScale_sq hK hx,firstMetricConformalFactor,div_eq_mul_inv,pow_two]
    exact mul_le_mul h11 (hB.1.diagonal_inverse_le hK hx 0)
      (inv_nonneg.mpr (hB.1.diagonal_entry_pos hK hx 0).le) hK.le
  exact pow_le_pow_left₀ (firstMetricScale_pos γ g₁ x).le
    ((sq_le_sq₀ (firstMetricScale_pos γ g₁ x).le hK.le).1 hc) _

theorem Background.firstMetricDensityFactor_jet_bounds {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField dim} {e : Frame dim}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m) {x : X dim} (hx : x ∈ Ω) :
    let a : ℝ := (dim-2 : ℕ)
    let P₁ := a * (K*|M ⟨1,by omega⟩|)
    let P₂ := a * (K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)
    ‖fderiv ℝ (firstMetricDensityFactor γ g₁) x‖ ≤ K^(dim-2)*P₁ ∧
    ‖fderiv ℝ (fderiv ℝ (firstMetricDensityFactor γ g₁)) x‖ ≤ K^(dim-2)*(P₂+P₁^2) := by
  let a : ℝ := (dim-2 : ℕ)
  let q := firstMetricConformalDepth γ g₁
  let F : X dim → ℝ := (-a) • q
  let P₁ := a * (K*|M ⟨1,by omega⟩|)
  let P₂ := a * (K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hq : ContDiffAt ℝ ∞ q x :=
    (hB.firstMetricConformalDepth_smooth hK).contDiffAt (hΩ.mem_nhds hx)
  have hf : ContDiffAt ℝ ∞ F x := hq.const_smul (-a)
  have hqjet := hB.firstMetricConformalDepth_jet_bounds hΩ hK hm hx
  have hFD : fderiv ℝ F = (-a) • fderiv ℝ q :=
    fderiv_const_smul_field _
  have hF₁ : ‖fderiv ℝ F x‖ ≤ P₁ := by
    rw [hFD]
    change ‖(-a) • fderiv ℝ q x‖ ≤ P₁
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hqjet.1 ha
  have hF₂ : ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ P₂ := by
    rw [hFD,congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ q) (-a)) x]
    change ‖(-a) • fderiv ℝ (fderiv ℝ q) x‖ ≤ P₂
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hqjet.2 ha
  have hEq : firstMetricDensityFactor γ g₁ = fun z => Real.exp (F z) := by
    funext z
    change Real.exp (-q z)^(dim-2) = Real.exp ((-a)*q z)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hSize : Real.exp (F x) ≤ K^(dim-2) := by
    rw [← show firstMetricDensityFactor γ g₁ x = Real.exp (F x) from congrFun hEq x]
    exact hB.firstMetricDensityFactor_le hK hx
  have hP₁ : 0 ≤ P₁ := by dsimp [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by dsimp [P₂]; positivity
  change ‖fderiv ℝ (firstMetricDensityFactor γ g₁) x‖ ≤ K^(dim-2)*P₁ ∧
    ‖fderiv ℝ (fderiv ℝ (firstMetricDensityFactor γ g₁)) x‖ ≤ K^(dim-2)*(P₂+P₁^2)
  rw [hEq]
  exact ⟨(norm_fderiv_exp_comp_le F x (hf.differentiableAt (by simp)) P₁ hF₁).trans
      (mul_le_mul_of_nonneg_right hSize hP₁),
    (norm_second_fderiv_exp_comp_le F x hf P₁ P₂ hP₁ hP₂ hF₁ hF₂).trans
      (mul_le_mul_of_nonneg_right hSize (add_nonneg hP₂ (sq_nonneg _)))⟩

lemma Elliptic.norm_frameVectorLinear_le {Ω : Set (X dim)} {K : ℝ} {g : MetricField dim}
    (hg : Elliptic Ω K g) (hK : 1 ≤ K) {y : X dim} (hy : y ∈ Ω) (e : Frame dim)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0) :
    ‖frameVectorLinear e y‖ ≤ K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  apply ContinuousLinearMap.opNorm_le_bound _ hKpos.le
  intro u
  rw [frameVectorLinear_apply]
  have hb := (hg.frameVector_norm_sq_bounds hKpos hy e he u).2
  have hKsq : K ≤ K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hKpos.le (norm_nonneg u))).mp
  have hMul := mul_le_mul_of_nonneg_right hKsq (sq_nonneg ‖u‖)
  nlinarith only [hb,hMul]

lemma frameVector_mem_disk (g : MetricField dim) (e : Frame dim) (y z : X dim) (L : ℝ)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hz : z ∈ closedBall (0 : X dim) L) : frameVector e y z ∈ disk g y L := by
  have hzNorm : ‖z‖ ≤ L := by simpa only [mem_closedBall,dist_zero_right] using hz
  change metricPair g y (frameVector e y z) (frameVector e y z) ≤ L^2
  rw [metricPair_frameVector_self g e y z he]
  exact (sq_le_sq₀ (norm_nonneg z) ((norm_nonneg z).trans hzNorm)).2 hzNorm

end CalderonN
