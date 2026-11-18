import Proof.Archive.SphereSobolevCompletion
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine harmonic coordinates suffice for strong measurability, by
convergence of the canonical finite harmonic partial sums. -/
lemma aestronglyMeasurable_sphereSobolev_of_coefficients
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (s : ℝ) (F : α → SphereSobolev s)
    (hF : ∀ k,AEStronglyMeasurable (fun x => sphereSobolevCoefficientL s k (F x)) μ) :
    AEStronglyMeasurable F μ := by
  have hPart (n : ℕ) : AEStronglyMeasurable (fun x => sphereSobolevPartialSum s n (F x)) μ := by
    have h := Finset.aestronglyMeasurable_sum (Finset.range n)
      (f:=fun k x => sphereSobolevSingleL s k (sphereSobolevCoefficientL s k (F x)))
      (fun k _ => (sphereSobolevSingleL s k).continuous.comp_aestronglyMeasurable (hF k))
    convert h using 1
    funext x
    simp only [sphereSobolevPartialSum,Finset.sum_apply]
  exact aestronglyMeasurable_of_tendsto_ae atTop hPart
    (Eventually.of_forall (fun x => tendsto_sphereSobolevPartialSum s (F x)))
end ShrinkingSpheres
