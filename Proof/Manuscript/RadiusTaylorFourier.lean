module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace CalderonPaper

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

/-- A fixed datum and phase can be included in radius differentiation under the
quantization integral. The hypothesis bounds the product of the symbol's
first radius derivative and the rapidly decaying transformed datum. -/
theorem hasDerivAt_radiusQuantization
    (a da : ℝ → A → ℂ) (v : A → ℂ) {O : Set ℝ} (hO : O ∈ 𝓝 (0:ℝ))
    (hMeas : ∀ r ∈ O, AEStronglyMeasurable (fun x => a r x * v x) μ)
    (hIntegrable : Integrable (fun x => a 0 x * v x) μ)
    (hdMeas : AEStronglyMeasurable (fun x => da 0 x * v x) μ)
    (B : A → ℝ) (hB : Integrable B μ)
    (hBound : ∀ᵐ x ∂μ, ∀ r ∈ O, ‖da r x‖ * ‖v x‖ ≤ B x)
    (hDeriv : ∀ᵐ x ∂μ, ∀ r ∈ O, HasDerivAt (fun s => a s x) (da r x) r) :
    Integrable (fun x => da 0 x * v x) μ ∧
    HasDerivAt (fun s => ∫ x, a s x * v x ∂μ) (∫ x, da 0 x * v x ∂μ) 0 := by
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => a s x * v x) (F' := fun s x => da s x * v x) (bound := B) hO
    (Filter.mem_of_superset hO hMeas) hIntegrable hdMeas ?_ hB ?_
  · simpa only [norm_mul] using hBound
  · filter_upwards [hDeriv] with x hx r hr
    let L : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ).flip (v x)
    simpa [L, mul_comm] using (hasDerivAt_const r L).clm_apply (hx r hr)

/-- A pointwise Taylor identity at a positive radius determines the integral
remainder by linearity. It also proves integrability of the remainder. -/
theorem integral_radiusTaylor_remainder
    (a₀ a₁ da remainder : A → ℂ) (r : ℝ) (hr : r ≠ 0)
    (h₀ : Integrable a₀ μ) (h₁ : Integrable a₁ μ) (hd : Integrable da μ)
    (hTaylor : ∀ x, a₁ x = a₀ x + r • da x + r^2 • remainder x) :
    Integrable remainder μ ∧
      (∫ x, a₁ x ∂μ) = (∫ x, a₀ x ∂μ) + r • (∫ x, da x ∂μ) +
        r^2 • (∫ x, remainder x ∂μ) := by
  have hrSq : r^2 ≠ 0 := pow_ne_zero _ hr
  have hRes : remainder = fun x => (r^2)⁻¹ • (a₁ x - (a₀ x + r • da x)) := by
    funext x
    have h : a₁ x - (a₀ x + r • da x) = r^2 • remainder x := by rw [hTaylor x]; abel
    rw [h, smul_smul, inv_mul_cancel₀ hrSq, one_smul]
  have hRest : Integrable remainder μ := by
    rw [hRes]
    exact (h₁.sub (h₀.add (hd.smul r))).smul ((r^2)⁻¹)
  refine ⟨hRest, ?_⟩
  calc
    (∫ x, a₁ x ∂μ) = ∫ x, (a₀ x + r • da x) + r^2 • remainder x ∂μ :=
      integral_congr_ae (Eventually.of_forall hTaylor)
    _ = _ := by
      change (∫ x, ((a₀ + r • da) x) + ((r^2 • remainder) x) ∂μ) = _
      rw [integral_add (h₀.add (hd.smul r)) (hRest.smul (r^2))]
      change (∫ x, a₀ x + (r • da) x ∂μ) + _ = _
      rw [integral_add h₀ (hd.smul r)]
      simp only [Pi.smul_apply, integral_smul]

end CalderonPaper
