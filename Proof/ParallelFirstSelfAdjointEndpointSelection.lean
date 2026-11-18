import Proof.UniformActualFirstErrorAdjointHigherEndpoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Select a single genuine higher-adjoint endpoint family before later
directions and tests, retaining the actual graph and pointwise norm budget.
No regularity of this selected family is inferred. -/
lemma exists_half_adjoint_higher_family {Y : Set X}
    (Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (B : X → ℝ)
    (hPoint : ∀ y ∈ Y,HalfAdjointHigherEndpointBound (Lo y) (B y)) :
    ∃ AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
        (Lo y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖AH y‖ ≤ B y := by
  classical
  have hPoint' (y : X) (hy : y ∈ Y) :
      ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
          (Lo y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖H‖ ≤ B y := hPoint y hy
  let AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    fun y => if hy : y ∈ Y then Classical.choose (hPoint' y hy) else 0
  refine ⟨AH,?_⟩
  intro y hy
  dsimp only [AH]
  rw [dite_eq_left hy]
  exact Classical.choose_spec (hPoint' y hy)

end ShrinkingSpheres.ParallelEnergy
