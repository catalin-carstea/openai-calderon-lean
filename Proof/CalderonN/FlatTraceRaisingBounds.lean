module

public import Proof.CalderonN.SmoothLinearTraceMultiplierBounds
public import Proof.CalderonN.FlatTraceRaisingAdjoint

import Mathlib.Tactic
import Proof.CalderonN.SmoothTraceHigherLift

/-! The flat raising operator is of angular order one on the error-form
levels, with a constant depending only on dimension. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothTraceRaising_uniform_angularBound (hn : 3 ≤ dim) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Module.End ℝ (SmoothSphereTrace dim)),
      SmoothTraceAngularBound hn 1 1 B →
      ∀ i : I dim, SmoothTraceAngularBound hn 1 C (smoothTraceRaising B i) := by
  let D := (2*(dim:ℝ))
  let M (j : I dim) := ((EuclideanSpace.proj (𝕜:=ℝ) j) : X dim →L[ℝ] ℝ)
  let c := 2*Real.sqrt ((dim:ℝ)+3)
  let C := max c (smoothTraceRotationLiftConstant dim c (c*2))
  have hC : 0 ≤ C := (by dsimp only [c]; positivity : 0 ≤ c).trans (le_max_left _ _)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C+∑ _ : I dim,D*C,by positivity,?_⟩
  intro B hB i
  have hM (j : I dim) : SmoothTraceAngularBound hn 0 C (smoothSphereTraceMul (smoothCoordinateData j)) := by
    have hEq : smoothCoordinateData j = smoothLinearTraceDatum (M j) := Subtype.ext rfl
    rw [hEq]
    have hMb : ‖M j‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro z
      rw [one_mul]
      exact PiLp.norm_apply_le z j
    simpa only [C,c,mul_one] using smoothLinearTraceDatum_multiplier_bound hn (M j) 1 zero_le_one hMb
  rw [smoothTraceRaising_eq_coordinate_rotation]
  have hT (j : I dim) := (smoothTraceRotation_angularBound hn j i).mul (hM j) hD
  have hN := SmoothTraceAngularBound.sum Finset.univ
    (fun j : I dim => smoothSphereTraceRotation j i*smoothSphereTraceMul (smoothCoordinateData j))
    (fun _ => D*C) (fun j _ => hT j)
  simpa only [Nat.add_zero,one_mul] using (hB.mul (hM i) zero_le_one).sub hN

end CalderonN
