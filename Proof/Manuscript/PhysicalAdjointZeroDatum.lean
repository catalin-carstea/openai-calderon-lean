module

public import Proof.Manuscript.PhysicalRadialAdjoint

import Proof.CalderonN.FixedBallPoissonCongruence
import Mathlib.Tactic

public section

noncomputable section

open Set Metric CalderonN
open scoped ContDiff

namespace CalderonPaper

open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The exact normalized adjoint sends the zero boundary datum to zero. -/
theorem radialBallVelocityAdjoint_zero_datum
    {M : MetricField dim} (V : X dim → X dim) (W : X dim → ℝ)
    {U : Set (X dim)} (hU : IsOpen U) (hBU : closedBall (0 : X dim) 1 ⊆ U)
    (hM : SmoothMetric U M) {z : X dim} (hz : z ∈ standardSphere dim) :
    radialBallVelocityAdjoint M V W 0 z = 0 := by
  have hSol : FixedBallSolution M 0 0 := by
    refine ⟨contDiff_const,fun _ _ => rfl,fun z hz => ?_⟩
    have h₀ (i : I dim) : coordDeriv i (0 : X dim → ℝ) = 0 := by
      funext x
      change fderiv ℝ (fun _ : X dim => (0 : ℝ)) x (axis i) = 0
      simp
    simp [laplace,h₀]
  have hd := fixedBallPoisson_fderiv_eq_of_solution hU hBU hM hSol
    (fun _ _ => rfl) (sphere_subset_closedBall hz)
  have hd' : fderiv ℝ (fixedBallPoisson M (fun _ => 0)) z z = 0 := by
    change fderiv ℝ (fixedBallPoisson M 0) z z = 0
    rw [hd]
    simp
  apply Complex.ext <;>
    simp [radialBallVelocityAdjoint, hd', sphereRotationDerivative]

end CalderonPaper
