import Proof.OperatorAdjointDerivativePairing
import Proof.RadialTaylorTrueAdjointPairing
import Proof.NormalFrameRadialAdjointTaylorModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

lemma normalFrame_taylor_true_adjoint_pairing (d : Data)
    (R Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (p : NormalFrameParameter)
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪(R p+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da p v⟫_ℝ) :
    ∀ u v : SphereSobolev 1,
      ⟪normalFrameRadialTaylorFamily d R p u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,normalFrameRadialAdjointTaylorFamily d Da p v⟫_ℝ :=
  radial_taylor_true_adjoint_pairing (R p) (Da p)
    (radialCorrectionCovectorL (normalFrameFirstCovector d.γ d.g₁ p)) p.2.1 hPair

/-- The actual angular Taylor derivatives retain true adjunction whenever
    the original full pairing holds along the SAME local curve. -/
theorem normalFrame_taylor_curve_derivative_adjoint (d : Data)
    (R Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (c : ℝ → NormalFrameParameter)
    (hR : DifferentiableAt ℝ (fun t => normalFrameRadialTaylorFamily d R (c t)) 0)
    (hDa : DifferentiableAt ℝ (fun t => normalFrameRadialAdjointTaylorFamily d Da (c t)) 0)
    (hPair : ∀ᶠ t : ℝ in 𝓝 0,∀ u v : SphereSobolev 1,
      ⟪(R (c t)+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da (c t) v⟫_ℝ) :
    ∀ u v : SphereSobolev 1,
      ⟪deriv (fun t => normalFrameRadialTaylorFamily d R (c t)) 0 u,
        sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
        deriv (fun t => normalFrameRadialAdjointTaylorFamily d Da (c t)) 0 v⟫_ℝ := by
  apply operator_derivative_adjoint_pairing _ _ _ _ hR.hasDerivAt hDa.hasDerivAt
  exact hPair.mono (fun t ht => normalFrame_taylor_true_adjoint_pairing d R Da (c t) ht)

end ShrinkingSpheres
