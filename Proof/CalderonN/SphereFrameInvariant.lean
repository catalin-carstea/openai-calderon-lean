module

public import Proof.CalderonN.FrameOperators
public import Proof.CalderonN.Moments

import Proof.CalderonN.OrthogonalSphereMeasure
import Proof.CalderonN.MetricPair
import Proof.CalderonN.NormalBallChart
import Mathlib.Tactic

/-! Adapted from `SphereFrameInvariant` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1800000

noncomputable section
open Set MeasureTheory

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

open OAI.AnisotropicCalderon.OrthogonalSphereMeasure

set_option backward.isDefEq.respectTransparency.types false

/-- Probability-sphere averaging is independent of the orthonormal
frame used to express the physical sphere. -/
theorem sphereAverage_eq_of_orthonormalFrames (γ : (MetricField dim)) (y : (X dim)) (e f : (Frame dim))
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hf : ∀ i j, metricPair γ y (f y i) (f y j) = if i = j then 1 else 0)
    (u : (X dim) → ℂ) :
    sphereAverage f y u = sphereAverage e y u := by
  let A := (frameCoordinatesL γ y (e y)).comp (frameVectorL (f y))
  let B := (frameCoordinatesL γ y (f y)).comp (frameVectorL (e y))
  have hn (w : (X dim)) : ‖A w‖ = ‖w‖ := by
    have hs : ‖A w‖^2 = ‖w‖^2 := by
      change ‖frameCoordinatesL γ y (e y) (frameVectorL (f y) w)‖^2 = _
      rw [frameCoordinatesL_apply,norm_frameCoordinates_sq _ _ _ _ he,frameVectorL_apply _ _ y]
      change metricPair γ y (frameVector f y w) (frameVector f y w) = _
      rw [metricPair_frameVector γ f y w w hf,EuclideanSpace.real_norm_sq_eq]
      simp only [pow_two]
    rw [← Real.sqrt_sq (norm_nonneg (A w)),hs,Real.sqrt_sq (norm_nonneg w)]
  let A' : (X dim) →ₗᵢ[ℝ] (X dim) := ⟨A.toLinearMap,hn⟩
  have hAB (w : (X dim)) : A (B w) = w := by
    change frameCoordinatesL γ y (e y) (frameVectorL (f y)
      (frameCoordinatesL γ y (f y) (frameVectorL (e y) w))) = w
    rw [frameVectorL_frameCoordinatesL γ y (f y) hf,frameCoordinatesL_frameVectorL γ y (e y) he]
  let T := LinearIsometryEquiv.ofSurjective A' (Function.RightInverse.surjective hAB)
  let R := orthogonalSphereHomeomorph T
  have hμ : MeasurePreserving R (sphereProbability dim) (sphereProbability dim) :=
    orthogonalSphereHomeomorph_sphereProbability_preserving T
  have hA (w : ↥(standardSphere dim)) : frameVector e y ((R w).val) = frameVector f y w := by
    rw [← frameVectorL_apply_frame, ← frameVectorL_apply_frame]
    change frameVectorL (e y) (A (w : (X dim))) = frameVectorL (f y) (w : (X dim))
    exact frameVectorL_frameCoordinatesL γ y (e y) he _
  change (∫ w : ↥(standardSphere dim), u (frameVector f y w) ∂(sphereProbability dim)) =
    ∫ w : ↥(standardSphere dim), u (frameVector e y w) ∂(sphereProbability dim)
  have h := hμ.integral_comp (Homeomorph.measurableEmbedding R)
    (fun w : ↥(standardSphere dim) => u (frameVector e y w))
  refine (integral_congr_ae ?_).trans h
  exact Filter.Eventually.of_forall (fun w => (congrArg u (hA w)).symm)

end CalderonN
