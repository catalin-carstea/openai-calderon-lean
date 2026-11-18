import Proof.NormalFrameCoefficientModel
import Proof.RadialCorrectionLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Smoothness of the actual first covector on the independent geometric
    parameter space, shared by forward and adjoint Taylor families. -/
theorem Background.contDiffOn_normalFrameFirstCovector {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (V : Set NormalFrameParameter) (hCenter : ∀ p ∈ V,p.1 ∈ Ω) :
    ContDiffOn ℝ ∞ (normalFrameFirstCovector d.γ d.g₁) V := by
  intro p hp
  have hEll := (h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds (hCenter p hp))
  have hBase : ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => firstDensityLogDifferential d.γ d.g₁ q.1) p :=
    ContDiffAt.comp (f := fun q : NormalFrameParameter => q.1) (g := firstDensityLogDifferential d.γ d.g₁) p hEll contDiffAt_fst
  exact (hBase.clm_comp contDiffAt_snd.snd).contDiffWithinAt

end ShrinkingSpheres
