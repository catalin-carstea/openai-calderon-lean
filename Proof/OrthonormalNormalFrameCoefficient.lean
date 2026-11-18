import Proof.NormalFrameGramNormalization
import Proof.NormalFrameCoefficientModel
import Proof.FirstMetricNormalCenterCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- The normalized independent extension agrees with the chosen frame on
the entire orthonormal locus, while preserving orthonormality off that locus. -/
def orthonormalNormalFrameCoefficient (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) : Mat :=
  normalFrameNormalizedCoefficient g g₁ E (normalizedOrthonormalFrameParameter g q.1,q.2)

lemma orthonormalNormalFrameCoefficient_eq (g g₁ : MetricField) (E : X × X → X)
    (p : NormalFrameParameter) (z : X)
    (he : ∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) :
    orthonormalNormalFrameCoefficient g g₁ E (p,z) = normalFrameNormalizedCoefficient g g₁ E (p,z) := by
  rw [orthonormalNormalFrameCoefficient,normalizedOrthonormalFrameParameter_eq_self g p he]

lemma normalFrameNormalizedLinear_radius_independent (g : MetricField) (y : X) (L : X →L[ℝ] X) (r s : ℝ) :
    normalFrameNormalizedLinear g (y,(r,L)) = normalFrameNormalizedLinear g (y,(s,L)) := rfl

lemma orthonormalNormalFrameCoefficient_framed (g g₁ : MetricField) (E : X × X → X)
    (e : Frame) (y z : X) (r : ℝ)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) :
    orthonormalNormalFrameCoefficient g g₁ E ((y,(r,frameVectorLinear e y)),z) =
      (firstMetricDensityFactor g g₁ y)⁻¹ • principalCoefficient (framedNormalMetric g₁ e E y r) z := by
  rw [orthonormalNormalFrameCoefficient_eq g g₁ E _ z
    (by simpa only [frameVectorLinear_apply,frameVector_axis] using he)]
  exact normalFrameNormalizedCoefficient_framed g g₁ E e y z r

/-- The normalized first-metric coefficient has exactly flat center value
for every orthonormal frame, including newly normalized independent frames. -/
lemma Background.normalFrameNormalizedCoefficient_zero {Y Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (r : ℝ) (L : X →L[ℝ] X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) :
    normalFrameNormalizedCoefficient g g₁ E ((y,(r,L)),(0:X)) = (1:Mat) := by
  let eL : Frame := fun _ i => L (axis i)
  have hL : frameVectorLinear eL y = L := by
    apply ContinuousLinearMap.ext
    intro v
    exact frameVector_linear_axes L y v
  have hFrame : ∀ i j,metricPair g y (eL y i) (eL y j) = if i=j then 1 else 0 := he
  have hFirst : framedNormalMetric g₁ eL E y r 0 = (firstMetricDensityFactor g g₁ y)^2 • (1:Mat) := by
    ext i j
    rw [hN.framedNormalMetric_center hy g₁ eL hFrame,h.firstMetricPair_eq_conformalFactor hK (hN.center_mem hy),
      ← h.firstMetricDensityFactor_sq hK (hN.center_mem hy),hFrame i j]
    rfl
  have hScale := principalCoefficient_radius_sq (fun _ : X => (1:Mat))
    (firstMetricDensityFactor g g₁ y) (firstMetricDensityFactor_pos _ _ _) (0:X) (by simp)
  have hFlat : principalCoefficient (fun _ : X => (1:Mat)) (0:X) = 1 := by
    simp [principalCoefficient,OAI.AnisotropicCalderon.vol]
  rw [hFlat] at hScale
  have hCoeff : principalCoefficient (framedNormalMetric g₁ eL E y r) 0 = firstMetricDensityFactor g g₁ y • (1:Mat) := by
    simpa only [principalCoefficient,OAI.AnisotropicCalderon.vol,hFirst] using hScale
  rw [← hL,normalFrameNormalizedCoefficient_framed,hCoeff,smul_smul,
    inv_mul_cancel₀ (firstMetricDensityFactor_pos g g₁ y).ne',one_smul]

/-- Every positive symmetric independent frame input has a flat zeroth
radial coefficient after the genuine Gram normalization. -/
lemma Background.orthonormalNormalFrameCoefficient_zero {Y Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {p : NormalFrameParameter} (hy : p.1 ∈ Y)
    (hs : ∀ u v,metricPair g p.1 (p.2.2 u) (p.2.2 v) = metricPair g p.1 (p.2.2 v) (p.2.2 u))
    (hp : ∀ u : X,u ≠ 0 → 0 < metricPair g p.1 (p.2.2 u) (p.2.2 u)) :
    orthonormalNormalFrameCoefficient g g₁ E (p,(0:X)) = (1:Mat) :=
  h.normalFrameNormalizedCoefficient_zero hK hN hy p.2.1 (normalFrameNormalizedLinear g p)
    (normalFrameNormalizedLinear_orthonormal g p hs hp)

lemma contDiffAt_orthonormalNormalFrameCoefficient (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X)
    (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) q.1.1)
    (hp : ∀ u : X,u ≠ 0 → 0 < metricPair g q.1.1 (q.1.2.2 u) (q.1.2.2 u))
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g₁ E)
      (normalFrameInput (normalizedOrthonormalFrameParameter g q.1,q.2)))
    (hc : ContDiffAt ℝ ∞ (firstMetricDensityFactor g g₁) q.1.1)
    (hPos : 0 < (normalFrameMetric g₁ E (normalizedOrthonormalFrameParameter g q.1,q.2)).det) :
    ContDiffAt ℝ ∞ (orthonormalNormalFrameCoefficient g g₁ E) q := by
  have hNorm := contDiffAt_normalizedOrthonormalFrameParameter g q.1 hg hp
  have hInput : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter × X =>
      (normalizedOrthonormalFrameParameter g p.1,p.2)) q :=
    (hNorm.comp q contDiffAt_fst).prodMk contDiffAt_snd
  exact (contDiffAt_normalFrameNormalizedCoefficient g g₁ E
    (normalizedOrthonormalFrameParameter g q.1,q.2) hT hc hPos).comp q hInput

end ShrinkingSpheres
