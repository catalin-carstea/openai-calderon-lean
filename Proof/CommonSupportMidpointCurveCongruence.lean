import Proof.RadialMidpointCoefficientCongruence
import Proof.Archive.CommonSupportMatrixInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A true master coefficient family and a separately constructed curve
    family give the same midpoint radial germ whenever their actual
    coefficients agree along the curve inside the normal ball. -/
theorem commonSupport_midpoint_curve_germ_congr
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0)
    (b : ℝ × X → Mat) (hb : ContDiff ℝ ∞ b) (T : Set X) (hT : IsCompact T)
    (hzB : ∀ t z,z ∉ T → b (t,z) = 0)
    (c : ℝ → P) (hc : ContinuousAt c 0)
    (V : Set P) (hV : IsOpen V) (h0V : c 0 ∈ V) (W : Set ℝ) (hW : IsOpen W) (h0W : (0:ℝ) ∈ W)
    (hValue : ∀ t ∈ W,c t ∈ V → ∀ z ∈ Metric.closedBall (0:X) 2,a (c t,z) = b (t,z))
    (R : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (Q : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (actualHighRadialErrorL (commonSupportMatrixFamily 2 a ha S hS hz p)))
    (hQ : ∀ t ∈ W,(Q t).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (actualHighRadialErrorL (commonSupportMatrixFamily 2 b hb T hT hzB t))) :
    (fun t => R (c t)) =ᶠ[𝓝 (0:ℝ)] Q := by
  have hC : ∀ᶠ t in 𝓝 (0:ℝ),c t ∈ V := hc.eventually (hV.mem_nhds h0V)
  have hBoth := hC.and (hW.mem_nhds h0W)
  apply midpoint_radial_family_germ_congr (fun t => R (c t)) Q
    (fun t => commonSupportMatrixFamily 2 a ha S hS hz (c t))
    (commonSupportMatrixFamily 2 b hb T hT hzB)
  · filter_upwards [hBoth] with t ht
    intro z hzBall
    rw [coefficientMatrixField_commonSupportMatrixFamily,coefficientMatrixField_commonSupportMatrixFamily]
    exact hValue t ht.2 ht.1 z (unitBall_subset_closedBall_two hzBall)
  · filter_upwards [hC] with t ht
    exact hR (c t) ht
  · filter_upwards [hW.mem_nhds h0W] with t ht
    exact hQ t ht

end ShrinkingSpheres
