import Proof.NormalizationStableNeighborhood
import Proof.NativeRelativeTaylorSmoothDomain
import Proof.NormalFrameRelativeResponseNormalization
import Proof.MidpointRadialAdjointOneInverse
import Proof.CommonSupportMidpointNeighborhood
import Proof.RadialTaylorTrueAdjointPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

structure SymmetricAdjointDomain (t : NormalFrameRelativeResponsePacket q) where
  domain : Set NormalFrameRelativeParameter
  domainOpen : IsOpen domain
  pointMem : ((y,frameVectorLinear d.frame y),0) ∈ domain
  sub : domain ⊆ t.domain
  normalizationStable : ∀ p ∈ domain,normalFrameRelativeNormalization d.γ p ∈ domain
  coercive : ∀ p ∈ domain,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp q.a q.smooth p))
  strong : ∀ p ∈ domain,(strongDirichletOperator fixedSobolevCalculus 0
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)).IsInvertible
  normal : ∀ p ∈ domain,(negativeBoundaryCoefficientMulL (normalCoefficientJet
    (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))).IsInvertible
  coefficientSymmetric : ∀ p ∈ domain,∀ᵐ z ∂((volume:Measure X).restrict ballOpens),
    (q.a (p,z)).IsSymm

/-- A previously chosen native packet has a genuine normalization-stable
    open inverse neighborhood carrying the SAME true radial and Taylor
    adjunctions throughout. No parameterwise operator selection is used. -/
theorem exists_native_symmetric_adjoint_domain (t : NormalFrameRelativeResponsePacket q)
    (hΩ : IsOpen Ω) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j)) = if i=j then 1 else 0)
    (F0 : SmoothCoefficientMatrix 2) (CI CW : ℝ) (point : NormalFrameRelativeNativePointData q F0 CI CW)
    (Vg : Set NormalFrameRelativeParameter) (hVg : IsOpen Vg)
    (hpG : ((y,frameVectorLinear d.frame y),0) ∈ Vg)
    (hSymG : ∀ p ∈ Vg,∀ z ∈ Metric.closedBall (0:X) 2,
      (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,z)).IsSymm) :
    Nonempty (SymmetricAdjointDomain t) := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  have hNormal0 : (negativeBoundaryCoefficientMulL (normalCoefficientJet (F p0))).IsInvertible := by
    rw [← commonSupport_negative_normal_multiplier_eq]
    exact point.normal
  obtain ⟨W,hW,hpW,hSub,hCoercive,hStrong,hNormal,R0,hR0,hRestrict0⟩ :=
    exists_commonSupport_midpoint_neighborhood q.a q.smooth q.support q.compact q.supported p0
      (t.domain ∩ Vg) (t.domainOpen.inter hVg) ⟨t.pointMem,hpG⟩ point.coercive point.strong hNormal0
  obtain ⟨V,hV,hp0V,hVW,hStable⟩ :=
    OAI.AnisotropicCalderon.exists_normalization_stable_neighborhood
      (normalFrameRelativeNormalization d.γ) (normalFrameRelativePositiveDomain Ω) W
      (isOpen_normalFrameRelativePositiveDomain hΩ) hW
      (h.contDiffOn_normalFrameRelativeNormalization hΩ hK).continuousOn
      (fun p hp => q.positive (t.sub (hSub hp).1))
      (fun p hp => h.normalFrameRelativeNormalization_idempotent hK p hp)
      p0 hpW (normalFrameRelativeNormalization_eq_self d.γ p0 he)
  have hSymmetric (p : NormalFrameRelativeParameter) (hp : p ∈ V) :
      ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(q.a (p,z)).IsSymm := by
    have hpD := (hSub (hVW hp)).1
    have hSym : ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(q.a (p,z)).IsSymm := by
      filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with z hz
      rw [(q.coefficientGerm p (t.sub hpD) z
        (Metric.closedBall_subset_closedBall hZ (unitBall_subset_closedBall_two hz))).eq_of_nhds]
      exact hSymG p (hSub (hVW hp)).2 z (unitBall_subset_closedBall_two hz)
    exact hSym
  exact ⟨⟨V,hV,hp0V,(fun p hp => (hSub (hVW hp)).1),hStable,
    (fun p hp => hCoercive p (hVW hp)),(fun p hp => hStrong p (hVW hp)),
    (fun p hp => hNormal p (hVW hp)),hSymmetric⟩⟩

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
