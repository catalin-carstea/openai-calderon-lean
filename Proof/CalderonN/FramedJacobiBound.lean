module

public import Proof.CalderonN.JacobiAcceleration
public import Proof.CalderonN.ParallelTransportODE

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The exact curvature equation and ellipticity give a framed
acceleration bound of order the squared physical speed. -/
theorem norm_framed_jacobiAcceleration_le
    {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    (F : ℝ → (I dim) → (X dim)) (hF : ∀ i, ContDiff ℝ ∞ (fun t => F t i))
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun u => F u i)
        (-connection g (q (0,s)) (timeVelocity q (0,s)) (F s i)) s) ∧
      ∀ i j, metricPair g (q (0,s)) (F s i) (F s j) = if i = j then 1 else 0)
    {B K r t : ℝ} (hB : 0 ≤ B) (hK : 0 < K) (ht : t ∈ Icc (0 : ℝ) 1)
    (hell : ∀ u, K⁻¹ * ‖u‖^2 ≤ metricPair g (q (0,t)) u u ∧
      metricPair g (q (0,t)) u u ≤ K * ‖u‖^2)
    (hcurv : ∀ v J : (X dim), ‖jacobiCurvatureTerm g (q (0,t)) v J‖ ≤ B * ‖v‖^2 * ‖J‖)
    (hspeed : metricPair g (q (0,t)) (timeVelocity q (0,t)) (timeVelocity q (0,t)) ≤ r^2) :
    let Z (s : ℝ) := frameCoordinates g (q (0,s)) (F s) (pathVariation q (0,s))
    ‖deriv (deriv Z) t‖ ≤ (B * K^2 * r^2) * ‖Z t‖ := by
  let x := q (0,t)
  let v := timeVelocity q (0,t)
  let J := pathVariation q (0,t)
  let Z (s : ℝ) := frameCoordinates g (q (0,s)) (F s) (pathVariation q (0,s))
  let W := jacobiCurvatureTerm g x v J
  obtain ⟨hZ,hEq⟩ := framed_variation_of_parallelFrame hg hq F hF hD
  have he := (hD t ht).self_of_nhds.2
  have hgeom : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      q (s,t) ∈ (univ : Set (X dim)) ∧ timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)) :=
    hfamily.mono fun s hs t ht => ⟨mem_univ _,hs t ht⟩
  have hSum := sum_deriv_deriv_smul_parallelFrame_eq_jacobiCurvature
    isOpen_univ hg hq hgeom F hZ ht (hEq t ht)
  change frameVector (fun _ => F t) x (deriv (deriv Z) t) = W at hSum
  have hAcc : deriv (deriv Z) t = frameCoordinates g x (F t) W := by
    rw [← hSum, frameCoordinates_frameVector g x _ _ he]
  have hSpeedE : ‖v‖^2 ≤ K*r^2 := by
    have h := (hell v).1.trans hspeed
    rw [inv_mul_eq_div,div_le_iff₀ hK] at h
    exact h.trans_eq (mul_comm _ _)
  have hJnorm : ‖J‖ ≤ Real.sqrt K * ‖Z t‖ := by
    have h := (hell J).1
    change K⁻¹ * ‖J‖^2 ≤ metricPair g x J J at h
    rw [← norm_frameCoordinates_sq g x J (F t) he,inv_mul_eq_div,div_le_iff₀ hK] at h
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hK.le, mul_comm K]
    exact h
  have hWnorm : ‖deriv (deriv Z) t‖ ≤ Real.sqrt K * ‖W‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hAcc,norm_frameCoordinates_sq g x W (F t) he,mul_pow,Real.sq_sqrt hK.le]
    exact (hell W).2
  have hC : ‖W‖ ≤ B * (K * r^2) * (Real.sqrt K * ‖Z t‖) :=
    (hcurv v J).trans (mul_le_mul (mul_le_mul_of_nonneg_left hSpeedE hB) hJnorm
      (norm_nonneg _) (by positivity))
  calc
    ‖deriv (deriv Z) t‖ ≤ Real.sqrt K * ‖W‖ := hWnorm
    _ ≤ Real.sqrt K * (B * (K * r^2) * (Real.sqrt K * ‖Z t‖)) :=
      mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg _)
    _ = (B * K^2 * r^2) * ‖Z t‖ := by
      have hs := Real.sq_sqrt hK.le
      linear_combination (B * K * r^2 * ‖Z t‖) * hs

/-- The second variation boundary form is bounded below by the framed
endpoint difference squared, with the quadratic error in the geodesic speed. -/
theorem framed_jacobi_boundary_lower_of_curvature
    {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hfamily : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
      timeVelocity (timeVelocity q) (s,t) =
        -connection g (q (s,t)) (timeVelocity q (s,t)) (timeVelocity q (s,t)))
    (F : ℝ → (I dim) → (X dim)) (hF : ∀ i, ContDiff ℝ ∞ (fun t => F t i))
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun u => F u i)
        (-connection g (q (0,s)) (timeVelocity q (0,s)) (F s i)) s) ∧
      ∀ i j, metricPair g (q (0,s)) (F s i) (F s j) = if i = j then 1 else 0)
    {B K r : ℝ} (hB : 0 ≤ B) (hK : 0 < K) (hr : B * K^2 * r^2 ≤ 1/2)
    (hell : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, K⁻¹ * ‖u‖^2 ≤ metricPair g (q (0,t)) u u ∧
      metricPair g (q (0,t)) u u ≤ K * ‖u‖^2)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v J : (X dim),
      ‖jacobiCurvatureTerm g (q (0,t)) v J‖ ≤ B * ‖v‖^2 * ‖J‖)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      metricPair g (q (0,t)) (timeVelocity q (0,t)) (timeVelocity q (0,t)) ≤ r^2) :
    let Z (s : ℝ) := frameCoordinates g (q (0,s)) (F s) (pathVariation q (0,s))
    ‖Z 1 - Z 0‖^2 - 2 * (B * K^2 * r^2) * (‖Z 0‖ + ‖Z 1‖)^2 ≤
      metricPair g (q (0,1)) (variationCovariantTime g q 0 1) (pathVariation q (0,1)) -
      metricPair g (q (0,0)) (variationCovariantTime g q 0 0) (pathVariation q (0,0)) := by
  let Z (s : ℝ) := frameCoordinates g (q (0,s)) (F s) (pathVariation q (0,s))
  obtain ⟨hZ,hRep⟩ := framed_variation_of_parallelFrame hg hq F hF hD
  have hZ' : ContDiff ℝ ∞ (deriv Z) :=
    (hZ.of_le (show ∞ + 1 ≤ ∞ by simp)).deriv'
  exact jacobi_variation_boundary_lower isOpen_univ hg hq (fun _ _ => mem_univ _) F
    Z (deriv Z) (deriv (deriv Z)) (hD 0 (by simp)).self_of_nhds.2
    (fun t ht => (hD t ht).self_of_nhds.1) (fun t ht => (hRep t ht).mono fun _ hs => hs.2)
    (fun t _ => (hZ.differentiable (by simp) t).hasDerivAt)
    (fun t _ => (hZ'.differentiable (by simp) t).hasDerivAt)
    (ε := B * K^2 * r^2) (by positivity) hr
    (fun t ht => norm_framed_jacobiAcceleration_le hg hq hfamily F hF hD hB hK ht
      (hell t ht) (hcurv t ht) (hspeed t ht))

end CalderonN
