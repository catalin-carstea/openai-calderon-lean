import Proof.ProfileRadiusJets
noncomputable section
set_option autoImplicit false
open Set
namespace ShrinkingSpheres

/-- Shared frame component estimate for the actual log-radius covector.
The derivation is extracted from the previously checked scaled-frame proof. -/
theorem frame_logRadius_component_bound (g : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0) (i : I) :
    |fderiv ℝ (fun x => Real.log (r x)) y (e y i)| ≤ beta g r y := by
  have hCs := covector_frame_cauchy g e y hFrame (fderiv ℝ (fun x => Real.log (r x)) y) (e y i)
  have hOne : (if i=i then (1:ℝ) else 0)=1 := by simp
  rw [hFrame i i,hOne,one_mul,← beta_sq g e r y hFrame] at hCs
  have hBeta0 : 0 ≤ beta g r y := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (abs_nonneg _) hBeta0).mp
  simpa only [sq_abs] using hCs
end ShrinkingSpheres
