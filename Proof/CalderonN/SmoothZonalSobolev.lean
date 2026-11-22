module

public import Proof.CalderonN.ComplexZonalProjection
public import Proof.CalderonN.SmoothAngularCasimir
import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN
open OAI.AnisotropicCalderon.SphereHarmonic

variable {n : ℕ} [NeZero n]

theorem smoothSphereLift_ae (F : X n → ℝ) (hF : ContDiff ℝ ∞ F) :
    smoothSphereLift F hF =ᵐ[unitSphereProbability n] fun w : UnitSphere n => F w.val := by
  exact (smoothSphereRestriction F hF).coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability n)

/-- Summability of the series defining the protected complex norm, for smooth
    functions in the frame coordinates. -/
theorem summable_sobolevSq_of_smooth_frame (hn : 3 ≤ n)
    (g : MetricField n) (e : Frame n) (y : X n)
    (he : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (hF : ContDiff ℝ ∞ (fun w => F (frameVector e y w))) (s : ℝ) :
    Summable (fun k : ℕ => (1 + (k : ℝ)) ^ (2 * s) * fiberSq e y (degreePart g e k y F)) := by
  let R : X n → ℝ := fun w => (F (frameVector e y w)).re
  let I : X n → ℝ := fun w => (F (frameVector e y w)).im
  have hR : ContDiff ℝ ∞ R := Complex.reCLM.contDiff.comp hF
  have hI : ContDiff ℝ ∞ I := Complex.imCLM.contDiff.comp hF
  let U := smoothSphereLift R hR
  let V := smoothSphereLift I hI
  have hU : U =ᵐ[unitSphereProbability n] fun w : UnitSphere n => (F (frameVector e y w.val)).re :=
    smoothSphereLift_ae R hR
  have hV : V =ᵐ[unitSphereProbability n] fun w : UnitSphere n => (F (frameVector e y w.val)).im :=
    smoothSphereLift_ae I hI
  simp_rw [fiberSq_degreePart_harmonicProjection_components hn g e y he F U V hU hV]
  obtain ⟨q, hq⟩ := exists_nat_ge (2 * s)
  have hsum := (summable_smooth_angular_weight_all hn q R hR).add
    (summable_smooth_angular_weight_all hn q I hI)
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hsum
  intro k
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) hq

end CalderonN
