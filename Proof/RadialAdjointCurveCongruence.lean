import Proof.RadialAdjointCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact coefficient agreement along a geometric curve identifies the
    actual adjoint formulas as a germ, retaining the chosen master response. -/
theorem commonSupport_radial_adjoint_curve_germ_congr
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (A : P × X → Mat) (hA : ContDiff ℝ ∞ A) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → A (p,z) = 0)
    (B : ℝ × X → Mat) (hB : ContDiff ℝ ∞ B) (SB : Set X) (hSB : IsCompact SB)
    (hzB : ∀ t z,z ∉ SB → B (t,z) = 0)
    (c : ℝ → P) (hc : ContinuousAt c 0) (V : Set P) (hV : IsOpen V) (h0V : c 0 ∈ V)
    (W : Set ℝ) (hW : IsOpen W) (h0W : (0:ℝ) ∈ W)
    (hValue : ∀ t ∈ W,c t ∈ V → ∀ z ∈ Metric.closedBall (0:X) 2,A (c t,z) = B (t,z))
    (D : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    (fun t => radialAdjointFromResponseL (commonSupportMatrixFamily 2 A hA S hS hz (c t)) (D (c t))) =ᶠ[𝓝 (0:ℝ)]
      fun t => radialAdjointFromResponseL (commonSupportMatrixFamily 2 B hB SB hSB hzB t) (D (c t)) := by
  filter_upwards [hc.eventually (hV.mem_nhds h0V),hW.mem_nhds h0W] with t htV htW
  apply radialAdjointFromResponseL_congr_sphere
  intro w
  rw [coefficientMatrixField_commonSupportMatrixFamily,coefficientMatrixField_commonSupportMatrixFamily]
  exact hValue t htW htV w.val
    (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property))

end ShrinkingSpheres
