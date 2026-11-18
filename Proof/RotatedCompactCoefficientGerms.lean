import Proof.CompactRotatedRemainderOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- Rotate a genuine compact representative while retaining joint germs,
including all spatial jets needed at the boundary of the enlarged ball. -/
theorem exists_rotated_compact_coefficient_germs
    (R B : X → Mat) (hB : ContDiff ℝ ∞ B) (hCompact : HasCompactSupport B)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,B =ᶠ[𝓝 z] R) (i j : I) :
    ∃ a : ℝ × X → Mat,∃ ha : ContDiff ℝ ∞ a,∃ L : ℝ,
      (∀ θ z,z ∉ Metric.closedBall (0:X) L → a (θ,z) = 0) ∧
      ∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a =ᶠ[𝓝 (θ,z)]
        (fun p : ℝ × X => coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((p.1,0),p.2)) := by
  obtain ⟨L,hL⟩ := hCompact.exists_bound_of_continuousOn
    (show ContinuousOn (fun z : X => z) (tsupport B) from continuous_id.continuousOn)
  let A : ℝ × X → Mat := fun p => B p.2
  have hA : ContDiff ℝ ∞ A := hB.comp contDiff_snd
  have hzA (p : ℝ) (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : A (p,z) = 0 := by
    by_contra hn
    exact hz (by rw [Metric.mem_closedBall,dist_zero_right];exact hL z (subset_closure hn))
  let a : ℝ × X → Mat := fun p => coordinateRotationPrincipalFamily i j A ((p.1,0),p.2)
  have ha : ContDiff ℝ ∞ a := (contDiff_coordinateRotationPrincipalFamily i j A hA).comp
    ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hz (θ : ℝ) (z : X) (hz : z ∉ Metric.closedBall (0:X) L) : a (θ,z) = 0 :=
    coordinateRotationPrincipalFamily_zero_outside i j A L hzA (θ,0) z hz
  refine ⟨a,ha,L,hz,?_⟩
  intro θ z hzB
  have hRot : coordinateRotation i j θ z ∈ Metric.closedBall (0:X) 2 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,coordinateRotation_norm] using hzB
  have hPull : ContinuousAt (fun p : ℝ × X => coordinateRotation i j p.1 p.2) (θ,z) :=
    (contDiff_coordinateRotation_of_smooth i j Prod.fst Prod.snd contDiff_fst contDiff_snd).continuous.continuousAt
  have hNear := (hRep _ hRot).comp_tendsto hPull.tendsto
  filter_upwards [hNear] with p hp
  change (coordinateRotationMatrix i j p.1).transpose*B (coordinateRotation i j p.1 p.2)*coordinateRotationMatrix i j p.1 =
    (coordinateRotationMatrix i j p.1).transpose*R (coordinateRotation i j p.1 p.2)*coordinateRotationMatrix i j p.1
  simpa only [Function.comp_def] using congrArg
    (fun T : Mat => (coordinateRotationMatrix i j p.1).transpose*T*coordinateRotationMatrix i j p.1) hp

end ShrinkingSpheres
