import Proof.PrincipalThirdCoefficientWeight
import Proof.PrincipalAdjointWeights
import Proof.ScalarPrincipalSharpTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def principalScalarThreeJetWeightBudget (K M1 M2 M3 C2 C3 : ℝ) : ℝ :=
  principalZeroBudget K+principalFirstBudget K M1+principalSecondBudget K M1 M2 C2+
    principalRadiusThirdWeightBudget K M1 M2 M3 C2 C3

lemma principalRadiusThirdWeightBudget_nonneg (K M1 M2 M3 C2 C3 : ℝ)
    (hK : 0 ≤ K) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) :
    0 ≤ principalRadiusThirdWeightBudget K M1 M2 M3 C2 C3 := by
  unfold principalRadiusThirdWeightBudget principalRadiusAllThreeJetBudget principalAllThreeJetBudget
    principalThirdEntryBudget profileRadiusThirdBudget profileLogThirdBudget
  positivity

lemma principalScalarThreeJetWeightBudget_nonneg (K M1 M2 M3 C2 C3 : ℝ)
    (hK : 0 ≤ K) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) :
    0 ≤ principalScalarThreeJetWeightBudget K M1 M2 M3 C2 C3 := by
  have h3 := principalRadiusThirdWeightBudget_nonneg K M1 M2 M3 C2 C3 hK hM1 hM2 hM3
  unfold principalScalarThreeJetWeightBudget principalZeroBudget principalFirstBudget principalSecondBudget
  positivity

/-- The actual scalar principal matrix has a common epsilon*beta budget through
order three. Lower jets retain their sharper weights in the earlier producers. -/
theorem scalar_principal_three_jet_weights {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2)
    (hD3 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x a b))) y‖ ≤ M3) (a b : I) :
    CoordinateScalarThreeJetBound (fun x => scalarPrincipalMatrix g g₂ r x a b) y
      (principalScalarThreeJetWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)*ε*beta g r y) := by
  let A := principalScalarThreeJetWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)
  let A0 := principalZeroBudget K
  let A1 := principalFirstBudget K M1
  let A2 := principalSecondBudget K M1 M2 (Cj 2)
  let A3 := principalRadiusThirdWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)
  let β := beta g r y
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hA0 : 0 ≤ A0 := by dsimp [A0,principalZeroBudget];positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1,principalFirstBudget];positivity
  have hA2 : 0 ≤ A2 := by dsimp [A2,principalSecondBudget];positivity
  have hA3 : 0 ≤ A3 := principalRadiusThirdWeightBudget_nonneg K M1 M2 M3 (Cj 2) (Cj 3) hK0 hM1 hM2 hM3
  have h0A : A0 ≤ A := by change A0 ≤ A0+A1+A2+A3;linarith
  have h1A : A1 ≤ A := by change A1 ≤ A0+A1+A2+A3;linarith
  have h2A : A2 ≤ A := by change A2 ≤ A0+A1+A2+A3;linarith
  have h3A : A3 ≤ A := by change A3 ≤ A0+A1+A2+A3;linarith
  have hA : 0 ≤ A := hA0.trans h0A
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβ2 : 1 ≤ β^2 := one_le_pow₀ hβ
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hgrow (C : ℝ) (hCA : C ≤ A) : C*ε ≤ A*ε*β := by
    calc
      C*ε ≤ A*ε := mul_le_mul_of_nonneg_right hCA hε
      _ ≤ A*ε*β := by nlinarith only [mul_le_mul_of_nonneg_left hβ (mul_nonneg hA hε)]
  have hSharp (i j : I) := scalar_principal_sharp_two_jet_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy
    M1 M2 hM1 hM2 hD hD2 a b i j
  have ha0 : |scalarPrincipalMatrix g g₂ r y a b| ≤ A0*ε/β^2 := (hSharp 0 0).1
  have ha1 (i : I) : |coordDeriv i (fun x => scalarPrincipalMatrix g g₂ r x a b) y| ≤ A1*ε/β := (hSharp i i).2.1
  have ha2 (i j : I) : |coordDeriv i (coordDeriv j (fun x => scalarPrincipalMatrix g g₂ r x a b)) y| ≤ A2*ε := (hSharp j i).2.2
  constructor
  · exact ha0.trans ((div_le_self (mul_nonneg hA0 hε) hβ2).trans (hgrow A0 h0A))
  · intro i
    exact (ha1 i).trans ((div_le_self (mul_nonneg hA1 hε) hβ).trans (hgrow A1 h1A))
  · intro i j
    exact (ha2 i j).trans (hgrow A2 h2A)
  · intro i j k
    have ht := principal_radius_third_weight hY h h₂ hK e hframe hp hf hε hε1 hs hy M1 M2 M3 hM1 hM2 hM3 hD hD2 hD3 a b i j k
    exact ht.trans (by change A3*ε*β ≤ A*ε*β;gcongr)

end ShrinkingSpheres
