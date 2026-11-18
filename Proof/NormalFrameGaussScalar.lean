import Proof.FramedNormalRadialCoefficient
import Proof.NormalFrameMetricPositive
import Proof.NormalFrameCoefficientModel
import Proof.NormalFrameNormalizationDomain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma Background.framedNormalMetric_conformal {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    (E : X × X → X) (eL : Frame) (y z : X) (r : ℝ)
    (hx : E (y,r • frameVector eL y z) ∈ Ω) :
    framedNormalMetric g₁ eL E y r z=
      (firstMetricDensityFactor g g₁ (E (y,r • frameVector eL y z)))^2 • framedNormalMetric g eL E y r z := by
  ext i j
  change metricPair g₁ _ _ _= _
  rw [h.firstMetricPair_eq_conformalFactor hK hx,← h.firstMetricDensityFactor_sq hK hx]
  rfl

lemma Background.normalFrameNormalizedCoefficient_radial_row {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (L : X →L[ℝ] X) (r : ℝ) (hr : r ≠ 0) (z : X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j))=if i=j then 1 else 0)
    (hv : r • L z ∈ interior (disk g y (R y))) :
    ∃ chi : ℝ,0 < chi ∧ ∀ j : I,
      ∑ i : I,z i*normalFrameNormalizedCoefficient g g₁ E ((y,(r,L)),z) i j=chi*z j := by
  have hDet := (hN.normalFrameMetric_posDef_of_orthonormal h.1 hK hy L r z he (interior_subset hv)).det_pos
  let eL : Frame := fun _ i => L (axis i)
  have hL : frameVectorLinear eL y=L := by
    apply ContinuousLinearMap.ext
    intro v
    exact frameVector_linear_axes L y v
  have hFrame : ∀ i j,metricPair g y (eL y i) (eL y j)=if i=j then 1 else 0 := he
  have hV : r • frameVector eL y z ∈ interior (disk g y (R y)) := by
    rw [← frameVectorLinear_apply,hL]
    exact hv
  have hx := hN.path_image hy (r • frameVector eL y z) (interior_subset hV)
    (by constructor <;> norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1)
  simp only [one_smul] at hx
  have hDF : 0 < (framedNormalMetric g eL E y r z).det := by
    simpa only [← normalFrameMetric_framed,hL] using hDet
  let c := firstMetricDensityFactor g g₁ (E (y,r • frameVector eL y z))
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hMetric := h.framedNormalMetric_conformal hK E eL y z r hx
  have hScale := principalCoefficient_radius_sq (framedNormalMetric g eL E y r) c hc z
    (isUnit_iff_ne_zero.mpr hDF.ne')
  have hCoeff : principalCoefficient (framedNormalMetric g₁ eL E y r) z=
      c • principalCoefficient (framedNormalMetric g eL E y r) z := by
    exact (show principalCoefficient (framedNormalMetric g₁ eL E y r) z=
        principalCoefficient (fun w => c^2 • framedNormalMetric g eL E y r w) z by
      simp only [principalCoefficient,OAI.AnisotropicCalderon.vol,hMetric,c]).trans hScale
  let chi := (firstMetricDensityFactor g g₁ y)⁻¹*c*Real.sqrt (framedNormalMetric g eL E y r z).det
  refine ⟨chi,mul_pos (mul_pos (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _)) hc) (Real.sqrt_pos.2 hDF),?_⟩
  intro j
  have hRad := hN.framedNormal_principal_radial_row hΩ h.1 hK hy (hN.center_mem hy) eL hFrame r hr z hV
    (isUnit_iff_ne_zero.mpr hDF.ne') j
  have hNorm := normalFrameNormalizedCoefficient_framed g g₁ E eL y z r
  have hNormL : normalFrameNormalizedCoefficient g g₁ E ((y,(r,L)),z)=
      (firstMetricDensityFactor g g₁ y)⁻¹ • (c • principalCoefficient (framedNormalMetric g eL E y r) z) := by
    simpa only [hL,hCoeff] using hNorm
  calc
    _ = ((firstMetricDensityFactor g g₁ y)⁻¹*c)*
        (∑ i : I,z i*principalCoefficient (framedNormalMetric g eL E y r) z i j) := by
      simp only [hNormL,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := (congrArg (fun q : ℝ => ((firstMetricDensityFactor g g₁ y)⁻¹*c)*q) hRad).trans (by dsimp only [chi];ring)
end ShrinkingSpheres
