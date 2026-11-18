import Proof.Localization

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ShrinkingSpheres

lemma continuous_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    {Y : Set X} (hY : IsOpen Y) (f : X → E) (hf : ContinuousOn f Y) (hsupp : tsupport f ⊆ Y) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y ∈ Y
  · exact hf.continuousAt (hY.mem_nhds hy)
  · have hout : y ∉ tsupport f := fun ht => hy (hsupp ht)
    apply (show ContinuousAt (fun _ : X => (0:E)) y from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hout] with x hx
    exact image_eq_zero_of_notMem_tsupport hx

/-- A locally continuous integration weight is sufficient when the other factor has
    compact closed support inside its domain. Exterior values do not affect the integral. -/
lemma integrable_local_weighted {Y : Set X} (hY : IsOpen Y) (weight Q : X → ℝ)
    (hw : ContinuousOn weight Y) (hQ : Continuous Q) (hc : HasCompactSupport Q)
    (hsupp : tsupport Q ⊆ Y) : Integrable (fun y => weight y*Q y) := by
  have hs : tsupport (fun y => weight y*Q y) ⊆ tsupport Q := by
    apply closure_minimal _ (isClosed_tsupport Q)
    intro y hy
    by_contra hn
    exact hy (by simp only [image_eq_zero_of_notMem_tsupport hn,mul_zero])
  exact (continuous_of_tsupport_subset hY _ (hw.mul hQ.continuousOn) (hs.trans hsupp)).integrable_of_hasCompactSupport
    hc.mul_left

end ShrinkingSpheres
