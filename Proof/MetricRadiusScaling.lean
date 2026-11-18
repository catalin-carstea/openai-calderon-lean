import Proof.MetricLaplacianDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.MetricOperator
open OAI.AnisotropicCalderon.ConnectionError

/-- Exact dimension-three scaling of the genuine divergence coefficient. -/
lemma principalCoefficient_radius_sq (g : MetricField) (r : ℝ) (hr : 0 < r)
    (x : X) (hDet : IsUnit (g x).det) :
    principalCoefficient (fun y => r^2 • g y) x = r • principalCoefficient g x := by
  letI : Invertible (r^2) := invertibleOfNonzero (pow_ne_zero 2 hr.ne')
  have hDensity : Real.sqrt (r^2 • g x).det = r^3*Real.sqrt (g x).det := by
    rw [Matrix.det_smul,Fintype.card_fin]
    have hPow : (r^2)^3 = (r^3)^2 := by ring
    rw [hPow,Real.sqrt_mul (sq_nonneg (r^3)),Real.sqrt_sq_eq_abs,abs_of_pos (pow_pos hr 3)]
  change Real.sqrt (r^2 • g x).det • (r^2 • g x)⁻¹ = r • (Real.sqrt (g x).det • (g x)⁻¹)
  rw [hDensity,Matrix.inv_smul (g x) (r^2) hDet,invOf_eq_inv,smul_smul,smul_smul]
  have hScalar : (r^3*Real.sqrt (g x).det)*(r^2)⁻¹ = r*Real.sqrt (g x).det := by
    field_simp [hr.ne']
  rw [hScalar]

lemma coordinateFluxDivergence_const_smul (r : ℝ) (Z : X → X) (x : X) :
    coordinateFluxDivergence (fun y => r • Z y) x = r*coordinateFluxDivergence Z x := by
  have hFun (i : I) : (fun y => (r • Z y) i) = r • (fun y => Z y i) := by
    funext y
    rfl
  unfold coordinateFluxDivergence
  simp_rw [hFun,fderiv_const_smul_field]
  simp only [Pi.smul_apply,_root_.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]

/-- The radius square in the full chart metric factors out of its divergence
    equation by exactly one radius in dimension three. -/
theorem Elliptic.flux_divergence_radius_sq {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (u : X → ℝ) (r : ℝ) (hr : 0 < r) {x : X} (hx : x ∈ Ω) :
    coordinateFluxDivergence (metricDivergenceFlux (fun y => r^2 • g y) u) x =
      r*coordinateFluxDivergence (metricDivergenceFlux g u) x := by
  have hFlux : metricDivergenceFlux (fun y => r^2 • g y) u =ᶠ[𝓝 x]
      (fun y => r • metricDivergenceFlux g u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have hCoeff := principalCoefficient_radius_sq g r hr y
      (isUnit_iff_ne_zero.mpr (hg.posDef hK hy).det_pos.ne')
    simp only [metricDivergenceFlux,hCoeff,map_smul,_root_.smul_apply]
  exact (coordinateFluxDivergence_congr_germ hFlux).trans (coordinateFluxDivergence_const_smul r _ x)

end ShrinkingSpheres
