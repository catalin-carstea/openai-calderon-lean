import Proof.PrincipalSecondCoefficientWeight
import Proof.PrincipalAdjointBudgetDefinitions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The SAME actual scalar matrix rP retains its sharp zero, first and
second coordinate weights. The original scalar three-jet caller and the
base-connection drift use this shared producer. -/
theorem scalar_principal_sharp_two_jet_weights {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2) (a b i j : I) :
    |scalarPrincipalMatrix g g₂ r y a b| ≤ principalZeroBudget K*ε/(beta g r y)^2 ∧
      |coordDeriv i (fun x => scalarPrincipalMatrix g g₂ r x a b) y| ≤
        principalFirstBudget K M1*ε/beta g r y ∧
      |coordDeriv j (coordDeriv i (fun x => scalarPrincipalMatrix g g₂ r x a b)) y| ≤
        principalSecondBudget K M1 M2 (Cj 2)*ε := by
  have h01 := principal_radius_zero_first_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy M1 hM1 hD a b i
  have h2 := principal_radius_second_weight hY h h₂ hK e hframe hp hf hε hε1 hs hy M1 M2 hM1 hM2 hD hD2 a b i j
  simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul,principalZeroBudget,principalFirstBudget,
    principalSecondBudget] using And.intro h01.1 (And.intro h01.2 h2)

end ShrinkingSpheres
