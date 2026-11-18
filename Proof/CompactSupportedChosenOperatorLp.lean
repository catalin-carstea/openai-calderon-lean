import Proof.CompactSupportedMeasurableMajorant

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace ShrinkingSpheres

def chosenOperatorSection {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set X}
    (A : ∀ y ∈ Y,E →L[ℝ] F) (U : X → E) (y : X) : F := by
  classical
  exact if hy : y ∈ Y then A y hy (U y) else 0

lemma chosenOperatorSection_eq_zero_of_source_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Y : Set X}
    (A : ∀ y ∈ Y,E →L[ℝ] F) (U : X → E) {y : X} (hU : U y=0) :
    chosenOperatorSection A U y=0 := by
  by_cases hy : y ∈ Y
  · simp only [chosenOperatorSection,dite_eq_left hy,hU,map_zero]
  · simp only [chosenOperatorSection,dite_eq_right hy]

/-- A common continuous operator-norm majorant gives the actual base Lp
domain of a chosen measurable section. No measurability or smoothness of
the chosen operator family itself is assumed. -/
lemma memLp_chosen_operator_section_of_continuous_majorant
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Y S : Set X} (hY : MeasurableSet Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (A : ∀ y ∈ Y,E →L[ℝ] F) (U : X → E) (hU : ContDiff ℝ ∞ U)
    (h0U : ∀ x ∉ S,U x=0)
    (hMeas : AEStronglyMeasurable (chosenOperatorSection A U) (volume.restrict Y))
    (B : X → ℝ) (hB : ContinuousOn B Y) (hA : ∀ y hy,‖A y hy‖ ≤ B y) (p : ℝ≥0∞) :
    MemLp (chosenOperatorSection A U) p (volume.restrict Y) := by
  apply memLp_of_compact_supported_continuousOn_majorant hY hS hSY _ hMeas
    (fun y hy hs => by simp only [chosenOperatorSection,dite_eq_left hy,h0U y hs,map_zero])
    (fun y => B y*‖U y‖) (hB.mul hU.continuous.continuousOn.norm)
  intro y hy
  simp only [chosenOperatorSection,dite_eq_left hy]
  exact ((A y hy).le_opNorm (U y)).trans (mul_le_mul_of_nonneg_right (hA y hy) (norm_nonneg _))

end ShrinkingSpheres
