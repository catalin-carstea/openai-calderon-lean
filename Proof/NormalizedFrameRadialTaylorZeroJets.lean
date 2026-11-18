import Proof.OrthonormalFirstRadialCoefficientModel
import Proof.NormalFrameFirstCovectorRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma normalFrameNormalizedCoefficient_radius_zero (g g₁ : MetricField) (E : X × X → X)
    (y : X) (L : X →L[ℝ] X) (z : X) :
    normalFrameNormalizedCoefficient g g₁ E ((y,(0,L)),z) =
      normalFrameNormalizedCoefficient g g₁ E ((y,(0,L)),(0:X)) := by
  have hM : normalFrameMetric g₁ E ((y,(0,L)),z) = normalFrameMetric g₁ E ((y,(0,L)),(0:X)) := by
    ext i j
    simp only [normalFrameMetric,normalFrameInput,zero_smul]
  ext i j
  simp only [normalFrameNormalizedCoefficient,matrixFamilyCoefficient,matrixFamilyDensity,hM]

def orthonormalFirstRadialModel (g g₁ : MetricField) (q : NormalFrameParameter × X) : Mat :=
  normalFrameFirstCovector g g₁ (normalizedOrthonormalFrameParameter g q.1) q.2 • (1:Mat)

def orthonormalCoefficientRadialRemainder (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) : Mat :=
  orthonormalNormalFrameCoefficient g g₁ E q-(1:Mat)-q.1.2.1 • orthonormalFirstRadialModel g g₁ q

lemma orthonormalFirstRadialModel_radius_independent (g g₁ : MetricField) (y : X)
    (L : X →L[ℝ] X) (z : X) (r s : ℝ) :
    orthonormalFirstRadialModel g g₁ ((y,(r,L)),z) = orthonormalFirstRadialModel g g₁ ((y,(s,L)),z) := rfl

/-- The universal normalized family has a flat value at radius zero for
all spatial inputs, on the whole genuine positive frame domain. -/
lemma Background.orthonormalCoefficient_radius_zero {Y Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {p : NormalFrameParameter} (hy : p.1 ∈ Y) (hp : p ∈ normalFramePositiveDomain Ω) (z : X) :
    orthonormalNormalFrameCoefficient g g₁ E ((p.1,(0,p.2.2)),z) = (1:Mat) := by
  have hOrth := normalFrameNormalizedLinear_orthonormal g p
    (fun u v => metricPair_symm g p.1 (p.2.2 u) (p.2.2 v) (h.1.2 p.1 hp.1).1)
    (h.1.normalFramePositiveDomain_pair_positive hK hp)
  change normalFrameNormalizedCoefficient g g₁ E ((p.1,(0,normalFrameNormalizedLinear g p)),z) = _
  rw [normalFrameNormalizedCoefficient_radius_zero]
  exact h.normalFrameNormalizedCoefficient_zero hK hN hy 0 _ hOrth

/-- The genuine normalized extension has the same scalar first radial
model at every independent positive frame parameter. -/
lemma Background.orthonormalCoefficient_first_radial {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {p : NormalFrameParameter} (hy : p.1 ∈ Y) (hp : p ∈ normalFramePositiveDomain Ω) (z : X) :
    HasDerivAt (fun s : ℝ => orthonormalNormalFrameCoefficient g g₁ E ((p.1,(s,p.2.2)),z))
      (orthonormalFirstRadialModel g g₁ (p,z)) 0 := by
  have hOrth := normalFrameNormalizedLinear_orthonormal g p
    (fun u v => metricPair_symm g p.1 (p.2.2 u) (p.2.2 v) (h.1.2 p.1 hp.1).1)
    (h.1.normalFramePositiveDomain_pair_positive hK hp)
  exact h.normalFrameNormalizedCoefficient_first_radial hY hΩ hK hN hy (normalFrameNormalizedLinear g p) hOrth z

lemma Background.orthonormalCoefficientRadialRemainder_zero {Y Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {p : NormalFrameParameter} (hy : p.1 ∈ Y) (hp : p ∈ normalFramePositiveDomain Ω) (z : X) :
    orthonormalCoefficientRadialRemainder g g₁ E ((p.1,(0,p.2.2)),z) = 0 := by
  rw [orthonormalCoefficientRadialRemainder,h.orthonormalCoefficient_radius_zero hK hN hy hp z,
    sub_self,zero_smul,sub_zero]

/-- Both the value and first radius derivative of the Taylor remainder
vanish identically over the genuine frame domain. Higher parameter jets
therefore have the required exact zero data before quantitative estimates. -/
lemma Background.orthonormalCoefficientRadialRemainder_first_zero {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {p : NormalFrameParameter} (hy : p.1 ∈ Y) (hp : p ∈ normalFramePositiveDomain Ω) (z : X) :
    HasDerivAt (fun s : ℝ => orthonormalCoefficientRadialRemainder g g₁ E ((p.1,(s,p.2.2)),z)) 0 0 := by
  have hFirst := h.orthonormalCoefficient_first_radial hY hΩ hK hN hy hp z
  have hModel := (hasDerivAt_id (0:ℝ)).smul_const (orthonormalFirstRadialModel g g₁ (p,z))
  have ht := (hFirst.sub (hasDerivAt_const (0:ℝ) (1:Mat))).sub hModel
  simp only [sub_zero,one_smul,sub_self] at ht
  convert ht using 1 <;> try rfl

lemma Background.contDiffAt_orthonormalCoefficientRadialRemainder {Ω : Set X}
    (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    (E : X × X → X) (q : NormalFrameParameter × X) (hp : q.1 ∈ normalFramePositiveDomain Ω)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g₁ E)
      (normalFrameInput (normalizedOrthonormalFrameParameter g q.1,q.2)))
    (hPos : 0 < (normalFrameMetric g₁ E (normalizedOrthonormalFrameParameter g q.1,q.2)).det) :
    ContDiffAt ℝ ∞ (orthonormalCoefficientRadialRemainder g g₁ E) q := by
  have hg (i j : I) := (h.1.1 i j).contDiffAt (hΩ.mem_nhds hp.1)
  have hPositive := h.1.normalFramePositiveDomain_pair_positive hK hp
  have hNorm := contDiffAt_normalizedOrthonormalFrameParameter g q.1 hg hPositive
  have hCoeff := contDiffAt_orthonormalNormalFrameCoefficient g g₁ E q hg hPositive hT
    ((h.firstMetricDensityFactor_smooth hK).contDiffAt (hΩ.mem_nhds hp.1)) hPos
  let pN := normalizedOrthonormalFrameParameter g q.1
  have hLog : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) pN.1 :=
    (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds hp.1)
  have hBase : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter => firstDensityLogDifferential g g₁ p.1) pN :=
    ContDiffAt.comp (f:=fun p : NormalFrameParameter => p.1) (g:=firstDensityLogDifferential g g₁)
      pN hLog contDiffAt_fst
  have hFirstN : ContDiffAt ℝ ∞ (normalFrameFirstCovector g g₁) pN := hBase.clm_comp contDiffAt_snd.snd
  have hFirstAt := hFirstN.comp q.1 hNorm
  have hModel : ContDiffAt ℝ ∞ (orthonormalFirstRadialModel g g₁) q :=
    ((hFirstAt.comp q contDiffAt_fst).clm_apply contDiffAt_snd).smul contDiffAt_const
  exact (hCoeff.sub contDiffAt_const).sub (contDiffAt_fst.snd.fst.smul hModel)

end ShrinkingSpheres
