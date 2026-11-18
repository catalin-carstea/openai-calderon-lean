import Proof.PrincipalDensityProductJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

/-- Uniform first/zero coefficients of the scalar formal-adjoint defect for the actual
    principal matrix rQ. These are the epsilon/beta and epsilon weights, respectively. -/
theorem scalar_principal_adjoint_coefficient_weights {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁)
    (hD₂ : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M₂) :
    (∀ i,|adjointFirstCoefficient (fun i => axis i) (metricDensity g) (scalarPrincipalMatrix g g₂ r) y i| ≤
      principalAdjointFirstBudget K M₁*ε/beta g r y) ∧
    |adjointZeroCoefficient (fun i => axis i) (metricDensity g) (scalarPrincipalMatrix g g₂ r) y| ≤
      principalAdjointZeroBudget K M₁ M₂ (Cj 2)*ε := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hβ : 0 < beta g r y := zero_lt_one.trans_le (hf.trans (hp.2 y hy).2.1)
  have hμpos := metricDensity_pos h hKpos hy
  have hweights (i j k l : I) := scalar_principal_density_product_two_jets hY h h₂ hK e hframe hp hf hε hε1 hs hy
    M₁ M₂ hM₁ hM₂ hD hD₂ i j k l
  constructor
  · intro i
    have ht := adjointFirstCoefficient_bound (fun i => axis i) (metricDensity g) (scalarPrincipalMatrix g g₂ r) y
      (metricDensity g y)⁻¹ (metricDensity g y*(densityFirstBudget K M₁*principalZeroBudget K+principalFirstBudget K M₁)*ε/beta g r y)
      (inv_nonneg.mpr hμpos.le) (le_of_eq (abs_of_pos (inv_pos.mpr hμpos)))
      (fun a b => by simpa only [OAI.AnisotropicCalderon.PrincipalCommutator.directionalFDeriv,coordDeriv,principalDensityProductFirstBudget] using (hweights a b b b).1) i
    convert ht using 1 <;> unfold principalAdjointFirstBudget <;> field_simp [hμpos.ne',hβ.ne'] <;> ring
  · have ht := adjointZeroCoefficient_bound (fun i => axis i) (metricDensity g) (scalarPrincipalMatrix g g₂ r) y
      (metricDensity g y)⁻¹ (metricDensity g y*(densitySecondBudget K M₁ M₂*principalZeroBudget K+
        2*densityFirstBudget K M₁*principalFirstBudget K M₁+principalSecondBudget K M₁ M₂ (Cj 2))*ε)
      (inv_nonneg.mpr hμpos.le) (le_of_eq (abs_of_pos (inv_pos.mpr hμpos)))
      (fun a b => by
        change |coordDeriv b (coordDeriv a (fun x => metricDensity g x*scalarPrincipalMatrix g g₂ r x a b)) y| ≤ _
        simpa only [principalDensityProductSecondBudget] using (hweights a b a b).2)
    convert ht using 1 <;> unfold principalAdjointZeroBudget <;> field_simp [hμpos.ne'] <;> ring

end ShrinkingSpheres
