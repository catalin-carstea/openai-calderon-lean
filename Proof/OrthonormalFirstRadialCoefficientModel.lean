import Proof.NormalFrameNormalizationDomain
import Proof.FirstMetricNormalRadialJet
import Proof.ParallelFirstMetricCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma Background.normalFrameMetric_density_factor {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    (E : X × X → X) (p : NormalFrameParameter × X) (hx : E (normalFrameInput p) ∈ Ω) :
    normalFrameMetric g₁ E p =
      (firstMetricDensityFactor g g₁ (E (normalFrameInput p)))^2 • normalFrameMetric g E p := by
  ext i j
  change metricPair g₁ _ _ _ = _
  rw [h.firstMetricPair_eq_conformalFactor hK hx,← h.firstMetricDensityFactor_sq hK hx]
  rfl

/-- The reference normal metric has zero first radial jet in every fixed
linear frame. Orthonormality is not needed for this derivative identity. -/
lemma Background.normalFrameMetric_first_radial_zero {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (L : X →L[ℝ] X) (z : X) :
    HasDerivAt (fun s : ℝ => normalFrameMetric g E ((y,(s,L)),z)) 0 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hN.normalPullbackMetricPair_first_zero hΩ h.1 hK hy (hN.center_mem hy) e
    (h.2.2.2.2.2.2.2 y (hN.center_mem hy)) (L z) (L (axis i)) (L (axis j))

/-- Exact first radial model for the normalized divergence coefficient in
any frame orthonormal at the selected center. This is independent of any
radius profile or its derivatives. -/
theorem Background.normalFrameNormalizedCoefficient_first_radial {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (L : X →L[ℝ] X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) (z : X) :
    HasDerivAt (fun s : ℝ => normalFrameNormalizedCoefficient g g₁ E ((y,(s,L)),z))
      (firstDensityLogDifferential g g₁ y (L z) • (1:Mat)) 0 := by
  let G : ℝ → Mat := fun s => normalFrameMetric g E ((y,(s,L)),z)
  let H : ℝ → Mat := fun s => normalFrameMetric g₁ E ((y,(s,L)),z)
  let C : Mat → Mat := fun A i j => Real.sqrt A.det*A⁻¹ i j
  let D : ℝ → ℝ := fun s => normalizedJointFirstDensityFactor g g₁ E (y,s • L z)
  have hFrame := h.2.2.2.2.2.2.2 y (hN.center_mem hy)
  have hG0 : G 0 = (1:Mat) := by
    ext i j
    change normalPullbackMetricPair g E y 0 (L z) (L (axis i)) (L (axis j)) = _
    rw [hN.normalPullbackMetricPair_zero hy e hFrame]
    exact he i j
  have hG := h.normalFrameMetric_first_radial_zero hΩ hK hN hy L z
  have hCSmooth : ContDiffAt ℝ ∞ C (1:Mat) := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact contDiffAt_matrix_density_inverse_entry (fun A : Mat => A) 1
      (fun k l => contDiffAt_pi.mp (contDiffAt_pi.mp contDiffAt_id k) l) (by simp) i j
  have hCF : HasFDerivAt C (fderiv ℝ C (1:Mat)) (G 0) := by
    rw [hG0]
    exact (hCSmooth.differentiableAt (by simp)).hasFDerivAt
  have hCoef : HasDerivAt (fun s => C (G s)) 0 0 := by
    simpa only [Function.comp_def,map_zero] using hCF.comp_hasDerivAt 0 hG
  have hC0 : C (G 0) = (1:Mat) := by rw [hG0];ext i j;simp [C]
  have hyΩ := hN.center_mem hy
  have hc := h.firstMetricDensityFactor_smooth hK
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ E (y,(0:X)) := hReg.contDiffAt
    (hU.mem_nhds (hTube ⟨hy,zero_mem_disk g y (R y)⟩))
  have hNum : ContDiffAt ℝ ∞ (fun p : X × X => firstMetricDensityFactor g g₁ (E p)) (y,0) :=
    (show ContDiffAt ℝ ∞ (firstMetricDensityFactor g g₁) (E (y,0)) from by
      rw [hN.exp_zero hy];exact hc.contDiffAt (hΩ.mem_nhds hyΩ)).comp (y,0) hE
  have hDen : ContDiffAt ℝ ∞ (fun p : X × X => firstMetricDensityFactor g g₁ p.1) (y,0) :=
    ContDiffAt.comp (f:=fun p : X × X => p.1) (g:=firstMetricDensityFactor g g₁) (y,0)
      (hc.contDiffAt (hΩ.mem_nhds hyΩ)) contDiffAt_fst
  have hD : ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ E) (y,0) :=
    hNum.div hDen (firstMetricDensityFactor_pos g g₁ y).ne'
  have hDF : HasFDerivAt (normalizedJointFirstDensityFactor g g₁ E)
      (fderiv ℝ (normalizedJointFirstDensityFactor g g₁ E) (y,0)) (y,(0:ℝ) • L z) := by
    rw [zero_smul]
    exact (hD.differentiableAt (by simp)).hasFDerivAt
  have hCurve : HasDerivAt (fun s : ℝ => (y,s • L z)) ((0:X),L z) 0 := by
    simpa only [Function.id_def,one_smul] using (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_id (0:ℝ)).smul_const (L z))
  have hDensity : HasDerivAt D (firstDensityLogDifferential g g₁ y (L z)) 0 := by
    have ht := hDF.comp_hasDerivAt 0 hCurve
    rw [h.normalized_joint_density_vertical_zero hY hΩ hK hN hy (L z)] at ht
    exact ht
  have hD0 : D 0 = 1 := by
    dsimp only [D]
    rw [zero_smul,hN.normalized_joint_density_zero hy]
  have hProduct := hDensity.smul hCoef
  rw [hC0,hD0,smul_zero,zero_add] at hProduct
  have hImage : ∀ᶠ s in 𝓝 (0:ℝ),E (y,s • L z) ∈ Ω := by
    have hEC : ContinuousAt E (y,(0:ℝ) • L z) := by
      rw [zero_smul]
      exact hE.continuousAt
    have hCompose : ContinuousAt (fun s : ℝ => E (y,s • L z)) 0 :=
      ContinuousAt.comp (f:=fun s : ℝ => (y,s • L z)) (g:=E) hEC hCurve.continuousAt
    apply hCompose.eventually
    change Ω ∈ 𝓝 (E (y,(0:ℝ) • L z))
    simpa only [zero_smul,hN.exp_zero hy] using hΩ.mem_nhds hyΩ
  have hDet : ∀ᶠ s in 𝓝 (0:ℝ),0 < (G s).det := by
    have hContinuous := continuous_id.matrix_det.continuousAt.comp hG.continuousAt
    exact hContinuous.eventually (isOpen_Ioi.mem_nhds (show 0 < (G 0).det by rw [hG0];simp))
  have hEq : (fun s : ℝ => normalFrameNormalizedCoefficient g g₁ E ((y,(s,L)),z)) =ᶠ[𝓝 (0:ℝ)]
      (fun s => D s • C (G s)) := by
    filter_upwards [hImage,hDet] with s hs hd
    ext i j
    have hScale := matrixFamilyCoefficient_scalar_sq G H s
      (firstMetricDensityFactor g g₁ (E (y,s • L z))) (firstMetricDensityFactor_pos _ _ _)
      (h.normalFrameMetric_density_factor hK E ((y,(s,L)),z) hs) (isUnit_iff_ne_zero.mpr hd.ne') i j
    change (firstMetricDensityFactor g g₁ y)⁻¹*matrixFamilyCoefficient H s i j = _
    rw [hScale]
    dsimp only [D,C,normalizedJointFirstDensityFactor,matrixFamilyCoefficient,matrixFamilyDensity,
      Matrix.smul_apply,smul_eq_mul]
    rw [div_eq_mul_inv]
    ring
  exact hProduct.congr_of_eventuallyEq hEq

end ShrinkingSpheres
