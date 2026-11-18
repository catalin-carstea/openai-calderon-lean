import Proof.ProductOutputCompletion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set MeasureTheory Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_sub_harmonicPartialSum_sq_le (n : ℕ) (u v : SphereL2) :
    ‖u-harmonicPartialSum n v‖^2 ≤ 2*‖u‖^2+2*‖v‖^2 := by
  have hBound := norm_sub_sq_le_center u (harmonicPartialSum n v) 0
  simp only [sub_zero] at hBound
  have hPN := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_harmonicPartialSum_le n v)
  linarith only [hBound,hPN]

lemma integrable_weighted_sub_partialSum_norm_sq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (w : A → ℝ) (hw : AEStronglyMeasurable w μ)
    (hw0 : ∀ᵐ x ∂μ,0 ≤ w x) (U V : A → SphereL2)
    (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hiU : Integrable (fun x => w x*‖U x‖^2) μ)
    (hiV : Integrable (fun x => w x*‖V x‖^2) μ) (n : ℕ) :
    Integrable (fun x => w x*‖U x-harmonicPartialSum n (V x)‖^2) μ := by
  apply ((hiU.const_mul 2).add (hiV.const_mul 2)).mono'
    (hw.mul ((hU.sub ((harmonicPartialSum n).continuous.comp_aestronglyMeasurable hV)).norm.pow 2))
  filter_upwards [hw0] with x hx
  change ‖w x*‖U x-harmonicPartialSum n (V x)‖^2‖ ≤ 2*(w x*‖U x‖^2)+2*(w x*‖V x‖^2)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (norm_sub_harmonicPartialSum_sq_le n (U x) (V x)) hx).trans_eq (by ring)

lemma tendsto_integral_weighted_sub_partialSum_norm_sq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (w : A → ℝ) (hw : AEStronglyMeasurable w μ)
    (hw0 : ∀ᵐ x ∂μ,0 ≤ w x) (U V : A → SphereL2)
    (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hiU : Integrable (fun x => w x*‖U x‖^2) μ)
    (hiV : Integrable (fun x => w x*‖V x‖^2) μ) :
    Tendsto (fun n : ℕ => ∫ x,w x*‖U x-harmonicPartialSum n (V x)‖^2 ∂μ) atTop
      (𝓝 (∫ x,w x*‖U x-V x‖^2 ∂μ)) := by
  have hDom := (hiU.const_mul 2).add (hiV.const_mul 2)
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*(w x*‖U x‖^2)+2*(w x*‖V x‖^2))
    (fun n => hw.mul ((hU.sub ((harmonicPartialSum n).continuous.comp_aestronglyMeasurable hV)).norm.pow 2)) hDom
  · intro n
    filter_upwards [hw0] with x hx
    change ‖w x*‖U x-harmonicPartialSum n (V x)‖^2‖ ≤ 2*(w x*‖U x‖^2)+2*(w x*‖V x‖^2)
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hx (sq_nonneg _))]
    exact (mul_le_mul_of_nonneg_left (norm_sub_harmonicPartialSum_sq_le n (U x) (V x)) hx).trans_eq (by ring)
  · exact Eventually.of_forall (fun x =>
      ((tendsto_const_nhds.sub (tendsto_harmonicPartialSum (V x))).norm.pow 2).const_mul (w x))

end ShrinkingSpheres
