import Proof.CommonSupportMultiplierGainRegularity
import Proof.NormalFrameFirstModelSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Shared actual witnesses for one gained operator family on the independent
center/radius/frame parameter space. Quantitative estimates are proved later
for this same family, rather than selecting a new operator in each direction. -/
structure NormalFrameMultiplierGainFamily (d : Data)
    (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (r0 : ℝ) (V : Set NormalFrameParameter) (p0 : NormalFrameParameter) where
  first : NormalFrameParameter × X → Mat
  first_smooth : ContDiff ℝ ∞ first
  first_support : Set X
  first_support_compact : IsCompact first_support
  first_vanish : ∀ p z,z ∉ first_support → first (p,z) = 0
  domain : Set NormalFrameParameter
  domain_open : IsOpen domain
  point_mem : p0 ∈ domain
  domain_subset : domain ⊆ V
  first_germ : ∀ p ∈ domain,∀ z ∈ Metric.closedBall (0:X) 2,
    first =ᶠ[𝓝 (p,z)] normalFrameScaledFirstModelCoefficient d.γ d.g₁ r0
  principal_mem : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
    (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz p) z) 0 0) ⊤
    ((volume:Measure X).restrict ballOpens)
  first_mem : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
    (coefficientMatrixField 2 (commonSupportMatrixFamily 2 first first_smooth first_support first_support_compact first_vanish p) z) 0 0) ⊤
    ((volume:Measure X).restrict ballOpens)
  gain_smooth : ∀ Q : SmoothCoefficientJets 3,
    let G := fun p => radialTaylorMultiplierCommutatorL
      (commonSupportMatrixFamily 2 A hA S hS hz p) F0
      (commonSupportMatrixFamily 2 first first_smooth first_support first_support_compact first_vanish p)
      (principal_mem p) ha0 (first_mem p) Q r0
    ContDiffOn ℝ ∞ G domain ∧ ContDiffOn ℝ ∞ (fun p => -realHalfOperatorAdjointL (G p)) domain

def NormalFrameMultiplierGainFamily.gain {d : Data}
    {A : NormalFrameParameter × X → Mat} {hA : ContDiff ℝ ∞ A}
    {S : Set X} {hS : IsCompact S} {hz : ∀ p z,z ∉ S → A (p,z) = 0}
    {F0 : SmoothCoefficientMatrix 2}
    {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)}
    {r0 : ℝ} {V : Set NormalFrameParameter} {p0 : NormalFrameParameter}
    (T : NormalFrameMultiplierGainFamily d A hA S hS hz F0 ha0 r0 V p0)
    (Q : SmoothCoefficientJets 3) (p : NormalFrameParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  radialTaylorMultiplierCommutatorL (commonSupportMatrixFamily 2 A hA S hS hz p) F0
    (commonSupportMatrixFamily 2 T.first T.first_smooth T.first_support T.first_support_compact T.first_vanish p)
    (T.principal_mem p) ha0 (T.first_mem p) Q r0

theorem Background.exists_normalFrame_multiplier_gain_family {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
    (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (V : Set NormalFrameParameter) (hV : IsOpen V) (hCenter : ∀ p ∈ V,p.1 ∈ Ω)
    (p0 : NormalFrameParameter) (hp0 : p0 ∈ V) (r0 : ℝ)
    (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) :
    Nonempty (NormalFrameMultiplierGainFamily d A hA S hS hz F0 ha0 r0 V p0) := by
  obtain ⟨A1,hA1,S1,hS1,hz1,U,hU,hpU,hUV,hFirst⟩ :=
    h.exists_normalFrame_scaled_first_model_family hΩ hK V hV hCenter p0 hp0 r0
  have ha : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    intro p
    simpa only [coefficientMatrixField_commonSupportMatrixFamily] using commonSupportEnergyMemLp A hA p
  have ha1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 p) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) := by
    intro p
    simpa only [coefficientMatrixField_commonSupportMatrixFamily] using commonSupportEnergyMemLp A1 hA1 p
  refine ⟨{ first := A1
            first_smooth := hA1
            first_support := S1
            first_support_compact := hS1
            first_vanish := hz1
            domain := U
            domain_open := hU
            point_mem := hpU
            domain_subset := hUV
            first_germ := hFirst
            principal_mem := ha
            first_mem := ha1
            gain_smooth := ?_ }⟩
  intro Q
  exact contDiffOn_commonSupport_multiplier_gain A A1 hA hA1 S S1 hS hS1 hz hz1 F0 ha ha1 ha0 Q
    (fun _ => r0) U contDiffOn_const (fun p hp => hStrong p (hUV hp)) (fun p hp => hCoercive p (hUV hp))

end ShrinkingSpheres
