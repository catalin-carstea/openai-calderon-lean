module

public import Proof.Manuscript.PhysicalRadialAdjointZero

import Proof.CalderonN.FixedBallPoissonCongruence
import Proof.CalderonN.NormalizedVelocityAtZero
import Mathlib.Tactic

public section

noncomputable section

open Set Metric CalderonN
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A constant rescaling of the radial weight cancels between the Poisson
boundary datum and the final outward derivative. -/
theorem radialBallVelocityAdjoint_const_mul_weight
    {M : MetricField dim} {V : X dim → X dim} {W : X dim → ℝ}
    {φ : X dim → ℂ} {U S : Set (X dim)} {c : ℝ} (hc : c ≠ 0)
    (hU : IsOpen U) (hS : IsOpen S) (hBU : closedBall (0 : X dim) 1 ⊆ U)
    (hSS : standardSphere dim ⊆ S) (hM : SmoothMetric U M)
    (hV : ContDiffOn ℝ ∞ V S) (hW : ContDiffOn ℝ ∞ W S) (hW₀ : ∀ z ∈ S, W z ≠ 0)
    (hφ : ContDiffOn ℝ ∞ φ S) {z : X dim} (hz : z ∈ standardSphere dim) :
    radialBallVelocityAdjoint M V (fun w => c * W w) φ z =
      radialBallVelocityAdjoint M V W φ z := by
  have hInner : ContDiffOn ℝ ∞ (fun x => ⟪x,V x⟫_ℝ) S := contDiffOn_id.inner ℝ hV
  have hR : ContDiffOn ℝ ∞ (fun x => (φ x).re) S := Complex.reCLM.contDiff.comp_contDiffOn hφ
  have hI : ContDiffOn ℝ ∞ (fun x => (φ x).im) S := Complex.imCLM.contDiff.comp_contDiffOn hφ
  have hApply (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f S) :
      (c*W z) * fderiv ℝ (fixedBallPoisson M (fun x => f x*⟪x,V x⟫_ℝ / (c*W x))) z z =
        W z * fderiv ℝ (fixedBallPoisson M (fun x => f x*⟪x,V x⟫_ℝ / W x)) z z := by
    let d (x : X dim) := f x*⟪x,V x⟫_ℝ / W x
    let b := fixedBallPoisson M d
    have hb : FixedBallSolution M d b :=
      fixedBallPoisson_solution hU hBU hM ⟨S,hS,hSS,(hf.mul hInner).div hW hW₀⟩
    have heq : EqOn (fun x => f x*⟪x,V x⟫_ℝ / (c*W x)) (fun w => c⁻¹*d w)
        (standardSphere dim) := by
      intro x hx
      dsimp only [d]
      simp only [div_eq_mul_inv,mul_inv]
      ring
    rw [fixedBallPoisson_fderiv_eq_of_solution hU hBU hM (hb.const_mul c⁻¹) heq
      (sphere_subset_closedBall hz), fderiv_const_mul (hb.1.differentiable (by simp) z)]
    simp only [smul_apply,smul_eq_mul]
    field_simp
    rfl
  apply Complex.ext
  · change _ * _ - _ = _ * _ - _
    rw [hApply _ hR]
  · change _ * _ - _ = _ * _ - _
    rw [hApply _ hI]

/-- The flat radius-zero formula with the common Gauss weight used for
the full open family. -/
theorem radialBallVelocityAdjoint_normalized_zero_weight_one
    {Y Ω : Set (X dim)} (hY : IsOpen Y)
    {γ g : MetricField dim} {E : X dim × X dim → X dim} {e : Frame dim} {ρ : X dim → ℝ}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E ρ)
    {y : X dim} (hy : y ∈ Y)
    (he : ∀ j k, metricPair γ y (e y j) (e y k) = if j=k then 1 else 0)
    {c : ℝ} (hc : 0 < c) (hγ : γ y = c • g y) (b : ℝ) (i : I dim)
    {M : MetricField dim} {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : X dim) 1 ⊆ U) (hSS : standardSphere dim ⊆ S)
    (hSU : S ⊆ U) (hS₀ : (0 : X dim) ∉ S) (hM : SmoothMetric U M)
    (hEq : EqOn (normalizedBallMetric g E e y 0) M (closedBall (0 : X dim) 1))
    {φ : X dim → ℂ} (hφ : ContDiffOn ℝ ∞ φ S) {z : X dim} (hz : z ∈ standardSphere dim) :
    let a := frameCoordinates γ y (e y) (axis i)
    radialBallVelocityAdjoint M (fun x => scaledNormalTraceVelocity γ E e y 0 b x (axis i))
      (sphereGaussWeight M 1) φ z = flatAngularVelocityAdjoint (fun x => a+b • x) φ z := by
  dsimp only
  let V (x : X dim) := scaledNormalTraceVelocity γ E e y 0 b x (axis i)
  let s := (Real.sqrt c⁻¹)^(dim-2)
  have hs : 0 < s := pow_pos (Real.sqrt_pos.mpr (inv_pos.mpr hc)) _
  have hvEq : V = fun x => frameCoordinates γ y (e y) (axis i)+b • x :=
    funext (fun x => scaledNormalTraceVelocity_zero hY hE hN hy he b x (axis i))
  have hv : ContDiffOn ℝ ∞ V S := by
    rw [hvEq]
    exact (contDiff_const.add (b • ContinuousLinearMap.id ℝ (X dim)).contDiff).contDiffOn
  have hW : sphereGaussWeight M 1 = fun w => s*sphereGaussWeight M s w := by
    funext w
    unfold sphereGaussWeight
    field_simp
  have hNorm := radialBallVelocityAdjoint_normalized_zero hY hE hN hy he hc hγ b i
    hU hS hBU hSS hSU hS₀ hM hEq hφ hz
  rw [hW,radialBallVelocityAdjoint_const_mul_weight hs.ne' hU hS hBU hSS hM hv
    ((sphereGaussWeight_contDiffOn hM s).mono hSU)
    (fun w hw => (sphereGaussWeight_pos hs (hM.2 w (hSU hw)) (fun ew => hS₀ (ew ▸ hw))).ne')
    hφ hz]
  exact hNorm

end CalderonPaper
