import Proof.NormalFrameRelativeNormalization
import Proof.RelativeAngularCoefficientCovariance
import Proof.FirstRadialAngularFieldJets
import Proof.NormalFrameRelativeActualCoefficientGerms
import Proof.NormalFrameRelativeActualParameter
import Proof.RelativeInverseRadiusFactorJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The normalized first-correction covector without the auxiliary
relative-radius factor carried by the affine first model. -/
def normalizedFirstCorrectionCovector (g g₁ : MetricField) (p : NormalFrameRelativeParameter) :
    X →L[ℝ] ℝ :=
  normalFrameFirstCovector g g₁ (normalFrameRelativeZeroL (normalFrameRelativeNormalization g p))

lemma normalizedFirstCorrectionCovector_eq_inverse_relative (g g₁ : MetricField)
    (p : NormalFrameRelativeParameter) (hp : 1+p.2 ≠ 0) :
    normalizedFirstCorrectionCovector g g₁ p =
      normalFrameRelativeInverseRadiusFactor p • normalFrameRelativeFirstCovector g g₁ p := by
  change _ = (1+p.2)⁻¹ • ((1+p.2) • normalizedFirstCorrectionCovector g g₁ p)
  rw [smul_smul,inv_mul_cancel₀ hp,one_smul]

lemma Elliptic.normalizedFirstCorrectionCovector_angular_curve {Ω : Set X}
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K) (g₁ : MetricField)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (i j : I) (θ : ℝ) :
    normalizedFirstCorrectionCovector g g₁ (normalFrameRelativeAngularCurve g p i j θ) =
      (normalizedFirstCorrectionCovector g g₁ p).comp
        (OAI.AnisotropicCalderon.SmoothSphereRotation.coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap := by
  have hFix := normalFrameRelativeNormalization_eq_self g
    (normalFrameRelativeAngularCurve g p i j θ) (h.normalFrameRelativeAngularCurve_orthonormal hK p hp i j θ)
  unfold normalizedFirstCorrectionCovector
  rw [hFix]
  apply ContinuousLinearMap.ext
  intro z
  rfl

lemma Background.normalizedFirstCorrectionCovector_smooth {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (normalizedFirstCorrectionCovector d.γ d.g₁)
      (normalFrameRelativePositiveDomain Ω) := by
  intro p hp
  have hN := (h.1.contDiffOn_normalFrameRelativeNormalization hΩ hK).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hp)
  have hD := (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds hp.1)
  have hD' : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter =>
      firstDensityLogDifferential d.γ d.g₁ q.1.1) p :=
    ContDiffAt.comp (f:=fun q : NormalFrameRelativeParameter => q.1.1)
      (g:=firstDensityLogDifferential d.γ d.g₁) p hD contDiffAt_fst.fst
  exact (hD'.clm_comp hN.fst.snd).contDiffWithinAt

lemma Background.normalizedFirstCorrectionCovector_actual_parameter {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (r0 : ℝ)
    {x : X} (hx : x ∈ Ω) :
    normalizedFirstCorrectionCovector d.γ d.g₁ (normalFrameRelativeActualParameter d r0 x) =
      firstDensityLogCovector d x := by
  have hFrame (i j : I) : metricPair d.γ x (frameVectorLinear d.frame x (axis i))
      (frameVectorLinear d.frame x (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 x hx i j
  unfold normalizedFirstCorrectionCovector
  rw [normalFrameRelativeNormalization_eq_self _ _ hFrame]
  exact (h.firstDensityLogCovector_eq_differential hK hΩ hx).symm

end ShrinkingSpheres
