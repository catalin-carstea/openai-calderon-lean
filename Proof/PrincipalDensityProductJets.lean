import Proof.PrincipalAdjointBudgetDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def principalDensityProductFirstBudget (K M1 : ℝ) : ℝ :=
  densityFirstBudget K M1*principalZeroBudget K+principalFirstBudget K M1

def principalDensityProductSecondBudget (K M1 M2 C2 : ℝ) : ℝ :=
  densitySecondBudget K M1 M2*principalZeroBudget K+
    2*densityFirstBudget K M1*principalFirstBudget K M1+principalSecondBudget K M1 M2 C2

theorem scalar_principal_density_product_two_jets {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁)
    (hD₂ : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M₂) (i j k l : I) :
    |coordDeriv k (fun x => metricDensity g x*scalarPrincipalMatrix g g₂ r x i j) y| ≤
      metricDensity g y*principalDensityProductFirstBudget K M₁*ε/beta g r y ∧
    |coordDeriv l (coordDeriv k (fun x => metricDensity g x*scalarPrincipalMatrix g g₂ r x i j)) y| ≤
      metricDensity g y*principalDensityProductSecondBudget K M₁ M₂ (Cj 2)*ε := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hβ : 0 < beta g r y := zero_lt_one.trans_le (hf.trans (hp.2 y hy).2.1)
  have hμpos := metricDensity_pos h hKpos hy
  have hμ := h.contDiffOn_density hKpos
  have hμ₁ (k : I) : |coordDeriv k (metricDensity g) y| ≤ densityFirstBudget K M₁*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hKpos hy M₁ M₂ hM₁ hM₂ hD hD₂ k k).1
  have hμ₂ (k l : I) : |coordDeriv l (coordDeriv k (metricDensity g)) y| ≤ densitySecondBudget K M₁ M₂*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hKpos hy M₁ M₂ hM₁ hM₂ hD hD₂ k l).2
  have ha (i j : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix g g₂ r x i j) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hp.1.mul (contDiffOn_principal_entry h h₂ hKpos i j)
  exact weighted_principal_entry_two_jets hY hμ (ha i j) hy
    (hf.trans (hp.2 y hy).2.1) hε hμpos
    (show 0 ≤ principalZeroBudget K by unfold principalZeroBudget; positivity)
    (show 0 ≤ principalFirstBudget K M₁ by unfold principalFirstBudget; positivity)
    (show 0 ≤ principalSecondBudget K M₁ M₂ (Cj 2) by unfold principalSecondBudget; positivity)
    (show 0 ≤ densityFirstBudget K M₁ by unfold densityFirstBudget; positivity)
    (show 0 ≤ densitySecondBudget K M₁ M₂ by unfold densitySecondBudget; positivity)
    hμ₁ hμ₂
    (show |scalarPrincipalMatrix g g₂ r y i j| ≤ principalZeroBudget K*ε/(beta g r y)^2 from by
      simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul,principalZeroBudget] using
        (principal_radius_zero_first_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy M₁ hM₁ hD i j k).1)
    (fun a => by simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul,principalFirstBudget] using
      (principal_radius_zero_first_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy M₁ hM₁ hD i j a).2)
    (fun a b => by simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul,principalSecondBudget] using
      principal_radius_second_weight hY h h₂ hK e hframe hp hf hε hε1 hs hy M₁ M₂ hM₁ hM₂ hD hD₂ i j a b) k l

end ShrinkingSpheres
