import Proof.AngularEnergyDensity

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace ShrinkingSpheres

lemma fiberSq_nonneg (e : Frame) (y : X) (u : X → ℂ) : 0 ≤ fiberSq e y u := by
  rw [fiberSq_integral_norm]
  exact integral_nonneg (fun _ => sq_nonneg _)

lemma sobolevSq_nonneg (g : MetricField) (e : Frame) (s : ℝ) (y : X) (u : X → ℂ) :
    0 ≤ sobolevSq g e s y u := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (fiberSq_nonneg e y _)

lemma physicalEnergyDensity_nonneg (g : MetricField) (e : Frame) (r : X → ℝ) (φ : Field) (y : X) :
    0 ≤ physicalEnergyDensity g e r φ y := by
  have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hH : 0 ≤ ∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)) :=
    Finset.sum_nonneg (fun _ _ => fiberSq_nonneg e y _)
  have hHs : 0 ≤ ∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)) :=
    Finset.sum_nonneg (fun _ _ => sobolevSq_nonneg g e _ y _)
  exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg
    (add_nonneg hH (mul_nonneg (sq_nonneg _) (sobolevSq_nonneg g e _ y _)))
    (mul_nonneg (inv_nonneg.mpr hb) hHs)) (mul_nonneg hb (sobolevSq_nonneg g e _ y _)))

lemma energySq_nonneg (Y : Set X) (g : MetricField) (e : Frame) (r : X → ℝ) (φ : Field) :
    0 ≤ energySq Y g e r φ := by
  rw [energySq_eq_integral_density]
  exact integral_nonneg (fun y => physicalEnergyDensity_nonneg g e r φ y)

lemma energyNorm_sq (Y : Set X) (d : Data) (φ : Field) :
    (energyNorm Y d φ)^2 = energySq Y d.γ d.frame d.radius φ :=
  Real.sq_sqrt (energySq_nonneg Y d.γ d.frame d.radius φ)

lemma outputSq_nonneg (Y : Set X) (g : MetricField) (e : Frame) (φ : Field) :
    0 ≤ outputSq Y g e φ :=
  integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (fiberSq_nonneg e y _))

lemma traceNorm_sq (Y : Set X) (d : Data) (φ : Field) :
    (traceNorm Y d φ)^2 = outputSq Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ) :=
  Real.sq_sqrt (outputSq_nonneg Y d.γ d.frame _)

end ShrinkingSpheres
