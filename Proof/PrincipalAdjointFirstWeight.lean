import Proof.PrincipalDensityProductJets
import Proof.LocalScalarAdjointFirstJet
import Proof.ScalarRelativeInverseJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def principalAdjointFirstDerivativeBudget (K M1 M2 C2 : ℝ) : ℝ :=
  6*(1+3*densityFirstBudget K M1)*
    (principalDensityProductFirstBudget K M1+principalDensityProductSecondBudget K M1 M2 C2)

theorem scalar_principal_adjoint_first_derivative_weight {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁)
    (hD₂ : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M₂) (i k : I) :
    |coordDeriv k (fun x => adjointFirstCoefficient (fun j => axis j)
      (metricDensity g) (scalarPrincipalMatrix g g₂ r) x i) y| ≤
        principalAdjointFirstDerivativeBudget K M₁ M₂ (Cj 2)*ε := by
  let D1 := densityFirstBudget K M₁
  let D2 := densitySecondBudget K M₁ M₂
  let E1 := principalDensityProductFirstBudget K M₁
  let E2 := principalDensityProductSecondBudget K M₁ M₂ (Cj 2)
  let N := 1+3*D1
  let μ := metricDensity g y
  let M := N*μ⁻¹
  let B1 := μ*E1*ε
  let B2 := μ*E2*ε
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hD1 : 0 ≤ D1 := by dsimp [D1,densityFirstBudget];positivity
  have hD2 : 0 ≤ D2 := by dsimp [D2,densitySecondBudget];positivity
  have hE1 : 0 ≤ E1 := by
    dsimp [E1,principalDensityProductFirstBudget,densityFirstBudget,principalZeroBudget,principalFirstBudget]
    positivity
  have hE2 : 0 ≤ E2 := by
    dsimp [E2,principalDensityProductSecondBudget,densitySecondBudget,densityFirstBudget,
      principalZeroBudget,principalFirstBudget,principalSecondBudget]
    positivity
  have hN1 : 1 ≤ N := by dsimp only [N];linarith only [hD1]
  have hN0 : 0 ≤ N := zero_le_one.trans hN1
  have hμpos : 0 < μ := metricDensity_pos h hKpos hy
  have hM : 0 ≤ M := by dsimp only [M];positivity
  have hB1 : 0 ≤ B1 := by dsimp only [B1];positivity
  have hβ : 1 ≤ beta g r y := hf.trans (hp.2 y hy).2.1
  have hμ := h.contDiffOn_density hKpos
  have hμ1 (j : I) : |coordDeriv j (metricDensity g) y| ≤ D1*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hKpos hy M₁ M₂ hM₁ hM₂ hD hD₂ j j).1
  have hμ2 (j l : I) : |coordDeriv j (coordDeriv l (metricDensity g)) y| ≤ D2*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hKpos hy M₁ M₂ hM₁ hM₂ hD hD₂ l j).2
  have hInv := scalar_inverse_relative_coordinate_jets (metricDensity g) y
    (hμ.contDiffAt (hY.mem_nhds hy)) hμpos D1 D2 hD1 hD2 hμ1 hμ2
  have hn : |(metricDensity g y)⁻¹| ≤ M := by
    rw [abs_of_pos (inv_pos.mpr hμpos)]
    dsimp only [M]
    exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hN1 (inv_nonneg.mpr hμpos.le))
  have hn1 : |coordDeriv k (fun x => (metricDensity g x)⁻¹) y| ≤ M := by
    apply (hInv.1 k).trans
    exact mul_le_mul_of_nonneg_right (show 3*D1 ≤ N by dsimp only [N];linarith) (inv_nonneg.mpr hμpos.le)
  have ha (a b : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix g g₂ r x a b) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hp.1.mul (contDiffOn_principal_entry h h₂ hKpos a b)
  have hpos (x : X) (hx : x ∈ Y) : metricDensity g x ≠ 0 := (metricDensity_pos h hKpos hx).ne'
  have hP1 (j : I) : |coordDeriv j (fun x => metricDensity g x*scalarPrincipalMatrix g g₂ r x i j) y| ≤ B1 := by
    have hh := (scalar_principal_density_product_two_jets hY h h₂ hK e hframe hp hf hε hε1 hs hy
      M₁ M₂ hM₁ hM₂ hD hD₂ i j j j).1
    exact hh.trans (div_le_self hB1 hβ)
  have hP2 (j : I) : |coordDeriv k (coordDeriv j (fun x => metricDensity g x*scalarPrincipalMatrix g g₂ r x i j)) y| ≤ B2 :=
    (scalar_principal_density_product_two_jets hY h h₂ hK e hframe hp hf hε hε1 hs hy
      M₁ M₂ hM₁ hM₂ hD hD₂ i j j k).2
  have hh := coordinate_adjointFirstCoefficient_bound hY (metricDensity g) (scalarPrincipalMatrix g g₂ r)
    hμ ha hpos hy i k M B1 B2 hM hn hn1 hP1 hP2
  have hCancel : 6*M*(B1+B2) = principalAdjointFirstDerivativeBudget K M₁ M₂ (Cj 2)*ε := by
    change 6*((1+3*D1)*μ⁻¹)*(μ*E1*ε+μ*E2*ε) = 6*(1+3*D1)*(E1+E2)*ε
    field_simp [hμpos.ne'] <;> ring
  exact hh.trans_eq hCancel

end ShrinkingSpheres
