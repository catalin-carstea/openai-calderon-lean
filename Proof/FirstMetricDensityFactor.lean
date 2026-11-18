import Proof.FirstMetricNormalizedEquation
import Proof.ExpJetBounds
import Proof.MetricRadiusScaling

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- The scalar multiplying the reference divergence coefficient in dimension three. -/
def firstMetricDensityFactor (γ g₁ : MetricField) (x : X) : ℝ :=
  Real.exp (-firstMetricConformalDepth γ g₁ x)

lemma firstMetricDensityFactor_pos (γ g₁ : MetricField) (x : X) :
    0 < firstMetricDensityFactor γ g₁ x := Real.exp_pos _

lemma Background.firstMetricDensityFactor_sq {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    (firstMetricDensityFactor γ g₁ x)^2 = firstMetricConformalFactor γ g₁ x := by
  rw [hB.firstMetricConformalFactor_eq_exp_depth hK hx]
  unfold firstMetricDensityFactor
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

lemma Background.firstMetricDensityFactor_le {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    firstMetricDensityFactor γ g₁ x ≤ K := by
  have hl := ((hB.1.2 x hx).2 (axis 0)).1
  have hu := ((hB.2.1.2 x hx).2 (axis 0)).2
  have hEntry (g : MetricField) : metricPair g x (axis 0) (axis 0) = g x 0 0 := by simp [metricPair,axis]
  rw [hEntry,norm_axis,one_pow,mul_one] at hl hu
  have hMul := mul_le_mul_of_nonneg_left hl (sq_nonneg K)
  have hCancel : K^2*K⁻¹ = K := by field_simp
  rw [hCancel] at hMul
  have hκ : firstMetricConformalFactor γ g₁ x ≤ K^2 :=
    (div_le_iff₀ (hB.1.diagonal_entry_pos hK hx 0)).mpr (hu.trans (by nlinarith only [hMul]))
  rw [← hB.firstMetricDensityFactor_sq hK hx] at hκ
  exact (sq_le_sq₀ (firstMetricDensityFactor_pos γ g₁ x).le hK.le).mp hκ

theorem Background.firstMetricDensityFactor_smooth {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (firstMetricDensityFactor γ g₁) Ω :=
  (hB.firstMetricConformalDepth_smooth hK).neg.exp

/-- The divergence coefficient transforms by exactly the canonical positive scalar. -/
theorem Background.firstMetric_principalCoefficient {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    principalCoefficient g₁ x = firstMetricDensityFactor γ g₁ x • principalCoefficient γ x := by
  have hMetric : g₁ x = (firstMetricDensityFactor γ g₁ x)^2 • γ x := by
    rw [hB.firstMetricDensityFactor_sq hK hx]
    exact hB.firstMetric_eq_conformalFactor hK hx
  have hScale := principalCoefficient_radius_sq γ (firstMetricDensityFactor γ g₁ x)
    (firstMetricDensityFactor_pos γ g₁ x) x (isUnit_iff_ne_zero.mpr (hB.1.posDef hK hx).det_pos.ne')
  exact (show principalCoefficient g₁ x =
    principalCoefficient (fun z => (firstMetricDensityFactor γ g₁ x)^2 • γ z) x by
      simp only [principalCoefficient,OAI.AnisotropicCalderon.vol,hMetric]).trans hScale

/-- Uniform first two scalar jets of the actual divergence density factor. -/
theorem Background.firstMetricDensityFactor_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) (hm : 2 ≤ m) {x : X} (hx : x ∈ Ω) :
    ‖fderiv ℝ (firstMetricDensityFactor γ g₁) x‖ ≤ K^2*|M ⟨1,by omega⟩| ∧
    ‖fderiv ℝ (fderiv ℝ (firstMetricDensityFactor γ g₁)) x‖ ≤
      K^2*|M ⟨2,by omega⟩|+2*K^3*|M ⟨1,by omega⟩|^2 := by
  let t := firstMetricConformalDepth γ g₁
  let T1 := K*|M ⟨1,by omega⟩|
  let T2 := K*|M ⟨2,by omega⟩|+K^2*|M ⟨1,by omega⟩|^2
  have hT1 : 0 ≤ T1 := by dsimp [T1];positivity
  have hT2 : 0 ≤ T2 := by dsimp [T2];positivity
  have ht := (hB.firstMetricConformalDepth_smooth hK).contDiffAt (hΩ.mem_nhds hx)
  have hJets := hB.firstMetricConformalDepth_jet_bounds hΩ hK hm hx
  have hD : ‖fderiv ℝ (fun y => -t y) x‖ ≤ T1 := by simpa only [fderiv_fun_neg,norm_neg] using hJets.1
  have hDD : ‖fderiv ℝ (fderiv ℝ (fun y => -t y)) x‖ ≤ T2 := by
    have hFun : fderiv ℝ (fun y => -t y) = -fderiv ℝ t := by funext y;exact fderiv_fun_neg
    rw [hFun,fderiv_neg,norm_neg]
    exact hJets.2
  have hq := hB.firstMetricDensityFactor_le hK hx
  constructor
  · exact (norm_fderiv_exp_comp_le (fun y => -t y) x (ht.neg.differentiableAt (by simp)) T1 hD).trans
      ((mul_le_mul_of_nonneg_right hq hT1).trans_eq (by dsimp [T1];ring))
  · exact (norm_second_fderiv_exp_comp_le (fun y => -t y) x ht.neg T1 T2 hT1 hT2 hD hDD).trans
      ((mul_le_mul_of_nonneg_right hq (add_nonneg hT2 (sq_nonneg _))).trans_eq (by dsimp [T1,T2];ring))

end ShrinkingSpheres
