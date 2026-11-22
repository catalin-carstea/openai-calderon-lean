module

public import Proof.Manuscript.RadiusTaylorFourier
public import Proof.Manuscript.RadiusReorderedAngular
public import Proof.Manuscript.MovingTraceSymbols

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- The first radius variation of a normalized angular operator, with
the center and every other geometric input held fixed. -/
@[expose] def radiusFirstSphereOperator {dim : ℕ} (e : (Q × ℝ) ≃ₗᵢ[ℝ] P)
    (A : P → SphereOperator dim) (p : P) : SphereOperator dim :=
  fun u w => deriv (fun s => A (e ((e.symm p).1,s)) u w) 0

/-- The exact quadratic remainder at a nonzero radius. Its chart symbols and
off-diagonal kernels are given by the smooth integral Taylor remainder. -/
@[expose] def radiusTaylorSphereOperator {dim : ℕ} (e : (Q × ℝ) ≃ₗᵢ[ℝ] P)
    (A : P → SphereOperator dim) (p : P) : SphereOperator dim :=
  fun u w => let r := (e.symm p).2
    (r^2)⁻¹ • (A p u w - A (e ((e.symm p).1,0)) u w - r • radiusFirstSphereOperator e A p u w)

theorem radiusSphereOperator_taylor_eq {dim : ℕ}
    (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (A : P → SphereOperator dim) (p : P)
    (u : CalderonN.X dim → ℂ) (w : CalderonN.X dim) (hr : (e.symm p).2 ≠ 0) :
    A p u w = A (e ((e.symm p).1,0)) u w +
      (e.symm p).2 • radiusFirstSphereOperator e A p u w +
      (e.symm p).2^2 • radiusTaylorSphereOperator e A p u w := by
  unfold radiusTaylorSphereOperator
  rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero _ hr),one_smul]
  abel

variable {ι : Type} [MeasurableSpace ι] {μ : Measure ι}

/-- An exact localized integral representation on a high-level parameter
neighborhood determines the localized radius derivative of the actual operator. -/
theorem radiusLocalized_derivative_of_quantization (A : ℝ → ℂ) (c : ℂ)
    (a da : ℝ → ι → ℂ) (v : ι → ℂ) {O : Set ℝ} (hO : O ∈ 𝓝 (0:ℝ))
    (hA : ∀ r ∈ O, c * A r = ∫ x, a r x * v x ∂μ)
    (hMeas : ∀ r ∈ O, AEStronglyMeasurable (fun x => a r x * v x) μ)
    (hInt : Integrable (fun x => a 0 x * v x) μ)
    (hdMeas : AEStronglyMeasurable (fun x => da 0 x * v x) μ)
    (B : ι → ℝ) (hB : Integrable B μ)
    (hBound : ∀ᵐ x ∂μ, ∀ r ∈ O, ‖da r x‖ * ‖v x‖ ≤ B x)
    (hDeriv : ∀ᵐ x ∂μ, ∀ r ∈ O, HasDerivAt (fun s => a s x) (da r x) r) :
    Integrable (fun x => da 0 x * v x) μ ∧
      c * deriv A 0 = ∫ x, da 0 x * v x ∂μ := by
  obtain ⟨hI,hD⟩ := hasDerivAt_radiusQuantization a da v hO hMeas hInt hdMeas B hB hBound hDeriv
  have hEq : (fun r => c * A r) =ᶠ[𝓝 (0:ℝ)] (fun r => ∫ x, a r x * v x ∂μ) :=
    Filter.mem_of_superset hO hA
  refine ⟨hI,?_⟩
  change c • deriv A 0 = _
  rw [← deriv_const_smul_field (𝕜 := ℝ) (𝕝 := ℂ) c A]
  exact hEq.deriv_eq.trans hD.deriv

/-- The localized operator remainder has precisely the integrated scalar
Taylor remainder, with no exchange of the two integrations required. -/
theorem radiusLocalized_remainder_of_quantization (A : ℝ → ℂ) (c : ℂ)
    (a da : ℝ → ι → ℂ) (aR v : ι → ℂ) (r : ℝ) (hr : r ≠ 0)
    (hEq₀ : c * A 0 = ∫ x, a 0 x * v x ∂μ)
    (hEq : c * A r = ∫ x, a r x * v x ∂μ)
    (hFirst : c * deriv A 0 = ∫ x, da 0 x * v x ∂μ)
    (hInt₀ : Integrable (fun x => a 0 x * v x) μ)
    (hInt : Integrable (fun x => a r x * v x) μ)
    (hIntFirst : Integrable (fun x => da 0 x * v x) μ)
    (hTaylor : ∀ x, a r x = a 0 x + r • da 0 x + r^2 • aR x) :
    Integrable (fun x => aR x * v x) μ ∧
      c * ((r^2)⁻¹ • (A r - A 0 - r • deriv A 0)) = ∫ x, aR x * v x ∂μ := by
  have hPair (x : ι) :
      a r x * v x = a 0 x * v x + r • (da 0 x * v x) + r^2 • (aR x * v x) := by
    rw [hTaylor x]
    simp only [Complex.real_smul,add_mul,mul_assoc]
  obtain ⟨hI,hQ⟩ := integral_radiusTaylor_remainder
    (fun x => a 0 x * v x) (fun x => a r x * v x)
    (fun x => da 0 x * v x) (fun x => aR x * v x) r hr hInt₀ hInt hIntFirst hPair
  rw [← hEq₀,← hEq,← hFirst] at hQ
  refine ⟨hI,?_⟩
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow] at hQ ⊢
  apply (mul_right_inj' (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr))).mp
  calc
    (r:ℂ)^2 * (c * (((r:ℂ)^2)⁻¹ * (A r - A 0 - (r:ℂ)*deriv A 0))) =
        c * A r - (c * A 0 + (r:ℂ)*(c * deriv A 0)) := by
      rw [show (r:ℂ)^2 * (c * (((r:ℂ)^2)⁻¹ * (A r - A 0 - (r:ℂ)*deriv A 0))) =
        c * (((r:ℂ)^2 * ((r:ℂ)^2)⁻¹) * (A r - A 0 - (r:ℂ)*deriv A 0)) by ring]
      rw [mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr)),one_mul]
      ring
    _ = (r:ℂ)^2 * ∫ x, aR x * v x ∂μ := by
      rw [hQ]
      abel

/-- Remove the common radius from the normalized adjoint Taylor identity,
after splitting the zero-radius response into its two flat operators. -/
theorem inverse_radius_taylor_split
    (r f : ℝ) (hr : r ≠ 0) (A T T₀ F₀ E₁ flat₁ flat₂ : ℂ)
    (hA : A = (r⁻¹:ℝ) • T)
    (hT : T = T₀ + r • F₀ + r^2 • E₁)
    (hT₀ : T₀ = flat₁ + (r*f) • flat₂) :
    A = (r⁻¹:ℝ) • flat₁ + f • flat₂ + r • E₁ + F₀ := by
  rw [hA,hT,hT₀]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hr]
  ring

end CalderonPaper
