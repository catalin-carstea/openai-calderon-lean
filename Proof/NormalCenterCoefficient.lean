import Proof.NormalCenterConformal
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- The first-metric divergence coefficient at the normal center is a positive
    scalar Euclidean coefficient, with the actual shared frame and normal map. -/
theorem Background.normal_center_principal_scalar {Y Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y) (r : ℝ) :
    ∃ c : ℝ,0 < c ∧ principalCoefficient (framedNormalMetric g₁ e expMap y r) 0 = c • (1:Mat) := by
  obtain ⟨a,ha,hCenter⟩ := hB.normal_center_conformal hN hy r
  refine ⟨Real.sqrt a,Real.sqrt_pos.2 ha,?_⟩
  have hh := principalCoefficient_const_scalar a ha (0:X)
  simpa only [principalCoefficient,OAI.AnisotropicCalderon.vol,hCenter] using hh

/-- Ellipticity bounds the positive scalar center coefficient in a fixed compact
    interval depending only on the same metric ellipticity constant. -/
theorem Elliptic.scalar_principal_coefficient_bounds {Ω : Set X} {K : ℝ} {H : MetricField}
    (hg : Elliptic Ω K H) (hK : 1 ≤ K) {x : X} (hx : x ∈ Ω) (c : ℝ)
    (hScalar : principalCoefficient H x = c • (1:Mat)) :
    (metricDensityBudget K)⁻¹*K⁻¹ ≤ c ∧ c ≤ metricDensityBudget K*K := by
  have hUE := hg.principalCoefficient_tau hK
  have hLo := hUE.lower_bound hx (axis 0)
  have hHi := hUE.upper_bound hx (axis 0) (axis 0)
  rw [hScalar] at hLo hHi
  have hLow : (metricDensityBudget K)⁻¹*K⁻¹ ≤ c := by
    simpa only [TauCeti.PDE.toQuadraticForm'_smul_one,norm_axis,one_pow,mul_one] using hLo
  have hHigh : |c| ≤ metricDensityBudget K*K := by
    simpa [axis,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct] using hHi
  exact ⟨hLow,(le_abs_self c).trans hHigh⟩

end ShrinkingSpheres
