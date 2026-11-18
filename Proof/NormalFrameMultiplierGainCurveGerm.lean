import Proof.NormalFrameMultiplierGainFamily
import Proof.NativeMultiplierGainCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
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

namespace NormalFrameMultiplierGainFamily
variable {d : Data} {A : NormalFrameParameter × X → Mat} {hA : ContDiff ℝ ∞ A}
  {S : Set X} {hS : IsCompact S} {hz : ∀ p z,z ∉ S → A (p,z) = 0}
  {F0 : SmoothCoefficientMatrix 2}
  {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
    ((volume:Measure X).restrict ballOpens)}
  {r0 : ℝ} {V : Set NormalFrameParameter} {p0 : NormalFrameParameter}
  (T : NormalFrameMultiplierGainFamily d A hA S hS hz F0 ha0 r0 V p0)

theorem gain_contDiffOn (Q : SmoothCoefficientJets 3) :
    ContDiffOn ℝ ∞ (T.gain Q) T.domain ∧
    ContDiffOn ℝ ∞ (fun p => -realHalfOperatorAdjointL (T.gain Q p)) T.domain :=
  T.gain_smooth Q

/-- Agreement of the actual principal and first coefficient fields along a
curve transfers its complete gained operator germ. Both cutoff choices and
all associated energy-integrability witnesses may differ. -/
theorem curve_germ
    (c : ℝ → NormalFrameParameter) (hc : ContinuousAt c 0) (hc0 : c 0 = p0)
    (B B1 : ℝ × X → Mat) (hB : ContDiff ℝ ∞ B) (hB1 : ContDiff ℝ ∞ B1)
    (SB SB1 : Set X) (hSB : IsCompact SB) (hSB1 : IsCompact SB1)
    (hzB : ∀ t z,z ∉ SB → B (t,z) = 0) (hzB1 : ∀ t z,z ∉ SB1 → B1 (t,z) = 0)
    (G0 : SmoothCoefficientMatrix 2)
    (hb : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 B hB SB hSB hzB t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hb1 : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 B1 hB1 SB1 hSB1 hzB1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hb0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (W : Set ℝ) (hW : IsOpen W) (h0W : (0:ℝ) ∈ W)
    (hValue : ∀ t ∈ W,c t ∈ T.domain → ∀ z ∈ Metric.closedBall (0:X) 2,
      A (c t,z) = B (t,z) ∧ T.first (c t,z) = B1 (t,z))
    (hBase : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z)
    (Q : SmoothCoefficientJets 3) :
    (fun t => T.gain Q (c t)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => radialTaylorMultiplierCommutatorL
        (commonSupportMatrixFamily 2 B hB SB hSB hzB t) G0
        (commonSupportMatrixFamily 2 B1 hB1 SB1 hSB1 hzB1 t) (hb t) hb0 (hb1 t) Q r0) := by
  have hcU : c 0 ∈ T.domain := by rw [hc0];exact T.point_mem
  have hFields : ∀ᶠ t in 𝓝 (0:ℝ),∀ z ∈ (ballOpens:Set X),
      A (c t,z) = B (t,z) ∧ T.first (c t,z) = B1 (t,z) := by
    filter_upwards [hW.mem_nhds h0W,hc.eventually (T.domain_open.mem_nhds hcU)] with t ht hct
    intro z hzBall
    exact hValue t ht hct z (unitBall_subset_closedBall_two hzBall)
  exact radialTaylorMultiplierCommutator_family_germ_congr
    (fun t => commonSupportMatrixFamily 2 A hA S hS hz (c t))
    (fun t => commonSupportMatrixFamily 2 T.first T.first_smooth T.first_support T.first_support_compact T.first_vanish (c t))
    (commonSupportMatrixFamily 2 B hB SB hSB hzB)
    (commonSupportMatrixFamily 2 B1 hB1 SB1 hSB1 hzB1) F0 G0
    (fun t => T.principal_mem (c t)) (fun t => T.first_mem (c t)) hb hb1 ha0 hb0 Q (fun _ => r0) 0
    (by
      filter_upwards [hFields] with t ht
      intro z hzBall
      simpa only [coefficientMatrixField_commonSupportMatrixFamily] using (ht z hzBall).1)
    (by
      filter_upwards [hFields] with t ht
      intro z hzBall
      simpa only [coefficientMatrixField_commonSupportMatrixFamily] using (ht z hzBall).2)
    hBase

end NormalFrameMultiplierGainFamily
end ShrinkingSpheres
