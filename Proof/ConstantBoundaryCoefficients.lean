import Proof.BoundaryGradientAdjoint
import Proof.UniformStrongDirichletInverse
import Proof.FrameCoordinateCovectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- One fixed compact scalar representative of one near the entire unit ball. -/
theorem exists_unit_boundary_coefficient : ∃ Q : SmoothCoefficientJets 2,
    ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)) := by
  obtain ⟨F0,hFlat⟩ := exists_flatCoefficientMatrix 2
  refine ⟨F0 0 0,?_⟩
  intro z hz
  have hz2 : z ∈ Metric.ball (0:X) 2 := by
    change dist z 0 < 2
    change dist z 0 ≤ 1 at hz
    linarith
  filter_upwards [Metric.isOpen_ball.mem_nhds hz2] with w hw
  have h := congrArg (fun A : Mat => A 0 0) (hFlat w (Metric.ball_subset_closedBall hw))
  exact h

def constantBoundaryCoefficient (Q : SmoothCoefficientJets 2) (c : ℝ) : SmoothCoefficientJets 2 := c • Q

theorem constantBoundaryCoefficient_germ (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (c : ℝ) (z : X) (hz : z ∈ Metric.closedBall (0:X) 1) :
    coefficientValue 2 (constantBoundaryCoefficient Q c) =ᶠ[𝓝 z] (fun _ => c) := by
  rw [constantBoundaryCoefficient,coefficientValue_smul]
  filter_upwards [hQ z hz] with w hw
  change c*coefficientValue 2 Q w = c
  rw [hw,mul_one]

theorem constantBoundaryCoefficient_local_C1 (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (c : ℝ) :
    LocalC1Bound (coefficientValue 2 (constantBoundaryCoefficient Q c)) |c| := by
  intro z hz
  have hEq := constantBoundaryCoefficient_germ Q hQ c z (Metric.ball_subset_closedBall hz)
  constructor
  · exact le_of_eq (congrArg abs hEq.eq_of_nhds)
  · rw [hEq.fderiv_eq,(hasFDerivAt_const (𝕜:=ℝ) c z).fderiv,norm_zero]
    exact abs_nonneg _

end ShrinkingSpheres
