module

public import Proof.CalderonN.WeightedHarmonicConvergence
import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Weighted output squares converge under harmonic truncation, with the original output
    square itself supplying domination. -/
theorem tendsto_integral_weighted_partialSum_norm_sq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (weight : A → ℝ) (hw : AEStronglyMeasurable weight μ)
    (hwpos : ∀ᵐ x ∂μ,0 ≤ weight x) (U : A → (SphereL2 dim)) (hU : AEStronglyMeasurable U μ)
    (hint : Integrable (fun x => weight x*‖U x‖^2) μ) :
    Tendsto (fun n : ℕ => ∫ x,weight x*‖harmonicPartialSum n (U x)‖^2 ∂μ)
      atTop (𝓝 (∫ x,weight x*‖U x‖^2 ∂μ)) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => weight x*‖harmonicPartialSum n (U x)‖^2) μ :=
    hw.mul (((harmonicPartialSum n).continuous.comp_aestronglyMeasurable hU).norm.pow 2)
  have hbound (n : ℕ) : ∀ᵐ x ∂μ,‖weight x*‖harmonicPartialSum n (U x)‖^2‖ ≤ weight x*‖U x‖^2 := by
    filter_upwards [hwpos] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_harmonicPartialSum_le n (U x))) hx
  have hlim : ∀ᵐ x ∂μ,Tendsto (fun n : ℕ => weight x*‖harmonicPartialSum n (U x)‖^2)
      atTop (𝓝 (weight x*‖U x‖^2)) := by
    apply Filter.Eventually.of_forall
    intro x
    exact ((tendsto_harmonicPartialSum (U x)).norm.pow 2).const_mul (weight x)
  exact tendsto_integral_of_dominated_convergence (fun x => weight x*‖U x‖^2) hmeas hint hbound hlim

lemma integrable_weighted_partialSum_norm_sq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (weight : A → ℝ) (hw : AEStronglyMeasurable weight μ)
    (hwpos : ∀ᵐ x ∂μ,0 ≤ weight x) (U : A → (SphereL2 dim)) (hU : AEStronglyMeasurable U μ)
    (hint : Integrable (fun x => weight x*‖U x‖^2) μ) (n : ℕ) :
    Integrable (fun x => weight x*‖harmonicPartialSum n (U x)‖^2) μ := by
  apply hint.mono' (hw.mul (((harmonicPartialSum n).continuous.comp_aestronglyMeasurable hU).norm.pow 2))
  filter_upwards [hwpos] with x hx
  change ‖weight x*‖harmonicPartialSum n (U x)‖^2‖ ≤ weight x*‖U x‖^2
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_harmonicPartialSum_le n (U x))) hx

end CalderonN
