import Proof.DensityThirdCoordinateJets
import Proof.ScalarRelativeInverseJets
import Proof.LocalScalarAdjointHigherJets
import Proof.PrincipalScalarThreeJetWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def densityAllThreeJetBudget (K M1 M2 M3 : ℝ) : ℝ :=
  1+densityFirstBudget K M1+densitySecondBudget K M1 M2+densityThirdBudget K M1 M2 M3

def densityInverseTwoJetBudget (K M1 M2 : ℝ) : ℝ :=
  1+3*densityFirstBudget K M1+9*densitySecondBudget K M1 M2+18*(densityFirstBudget K M1)^2

def principalAdjointSecondWeightBudget (K M1 M2 M3 C2 C3 : ℝ) : ℝ :=
  192*densityInverseTwoJetBudget K M1 M2*densityAllThreeJetBudget K M1 M2 M3*
    principalScalarThreeJetWeightBudget K M1 M2 M3 C2 C3

def principalAdjointZeroFirstWeightBudget (K M1 M2 M3 C2 C3 : ℝ) : ℝ :=
  144*densityInverseTwoJetBudget K M1 M2*densityAllThreeJetBudget K M1 M2 M3*
    principalScalarThreeJetWeightBudget K M1 M2 M3 C2 C3

/-- The differentiated scalar-adjoint coefficients needed by the principal error
algebra have their epsilon*beta weights for every admitted radius and frame.
The supplied generic adjoint estimates are fed by actual local density/rQ jets. -/
theorem scalar_principal_adjoint_higher_coefficient_weights {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2)
    (hD3 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x a b))) y‖ ≤ M3) :
    (∀ i k l,|coordDeriv k (coordDeriv l (fun x => adjointFirstCoefficient (fun j => axis j)
      (metricDensity g) (scalarPrincipalMatrix g g₂ r) x i)) y| ≤
      principalAdjointSecondWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)*ε*beta g r y) ∧
    (∀ k,|coordDeriv k (adjointZeroCoefficient (fun j => axis j) (metricDensity g) (scalarPrincipalMatrix g g₂ r)) y| ≤
      principalAdjointZeroFirstWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)*ε*beta g r y) := by
  let D1 := densityFirstBudget K M1
  let D2 := densitySecondBudget K M1 M2
  let D3 := densityThirdBudget K M1 M2 M3
  let D := densityAllThreeJetBudget K M1 M2 M3
  let N := densityInverseTwoJetBudget K M1 M2
  let A := principalScalarThreeJetWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)
  let β := beta g r y
  let M := N*(metricDensity g y)⁻¹
  let B := 8*(D*metricDensity g y)*(A*ε*β)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  have hD10 : 0 ≤ D1 := by dsimp [D1,densityFirstBudget];positivity
  have hD20 : 0 ≤ D2 := by dsimp [D2,densitySecondBudget];positivity
  have hD30 : 0 ≤ D3 := by
    dsimp [D3,densityThirdBudget,densityFirstBudget,densitySecondBudget,densityTraceFirstBudget,densityTraceSecondBudget]
    positivity
  have hD1le : D1 ≤ D := by change D1 ≤ 1+D1+D2+D3;linarith
  have hD2le : D2 ≤ D := by change D2 ≤ 1+D1+D2+D3;linarith
  have hD3le : D3 ≤ D := by change D3 ≤ 1+D1+D2+D3;linarith
  have hDOne : 1 ≤ D := by change 1 ≤ 1+D1+D2+D3;linarith
  have hD0 : 0 ≤ D := zero_le_one.trans hDOne
  have hNOne : 1 ≤ N := by change 1 ≤ 1+3*D1+9*D2+18*D1^2;nlinarith only [hD10,hD20,sq_nonneg D1]
  have hN1 : 3*D1 ≤ N := by change 3*D1 ≤ 1+3*D1+9*D2+18*D1^2;nlinarith only [hD20,sq_nonneg D1]
  have hN2 : 9*D2+18*D1^2 ≤ N := by change 9*D2+18*D1^2 ≤ 1+3*D1+9*D2+18*D1^2;linarith only [hD10]
  have hN0 : 0 ≤ N := zero_le_one.trans hNOne
  have hA0 : 0 ≤ A := principalScalarThreeJetWeightBudget_nonneg K M1 M2 M3 (Cj 2) (Cj 3) hK0 hM1 hM2 hM3
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hμpos := metricDensity_pos h hKpos hy
  have hμ := h.contDiffOn_density hKpos
  have hpos (x : X) (hx : x ∈ Y) : metricDensity g x ≠ 0 := (metricDensity_pos h hKpos hx).ne'
  have hμ1 (i : I) : |coordDeriv i (metricDensity g) y| ≤ D1*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hKpos hy M1 M2 hM1 hM2 hD hD2 i i).1
  have hμ2 (i j : I) : |coordDeriv i (coordDeriv j (metricDensity g)) y| ≤ D2*metricDensity g y :=
    (h.relative_density_coordinate_jets hY hKpos hy M1 M2 hM1 hM2 hD hD2 j i).2
  have hμ3 (i j k : I) : |coordDeriv i (coordDeriv j (coordDeriv k (metricDensity g))) y| ≤ D3*metricDensity g y :=
    h.relative_density_coordinate_third hY hKpos hy M1 M2 M3 hM1 hM2 hM3 hD hD2 hD3 i j k
  have hμAll : CoordinateScalarThreeJetBound (metricDensity g) y (D*metricDensity g y) := by
    constructor
    · rw [abs_of_pos hμpos]
      nlinarith only [mul_le_mul_of_nonneg_right hDOne hμpos.le]
    · intro i;exact (hμ1 i).trans (mul_le_mul_of_nonneg_right hD1le hμpos.le)
    · intro i j;exact (hμ2 i j).trans (mul_le_mul_of_nonneg_right hD2le hμpos.le)
    · intro i j k;exact (hμ3 i j k).trans (mul_le_mul_of_nonneg_right hD3le hμpos.le)
  have hInv := scalar_inverse_relative_coordinate_jets (metricDensity g) y
    (hμ.contDiffAt (hY.mem_nhds hy)) hμpos D1 D2 hD10 hD20 hμ1 hμ2
  have hM : 0 ≤ M := by dsimp [M];positivity
  have hn : |(metricDensity g y)⁻¹| ≤ M := by
    rw [abs_of_pos (inv_pos.mpr hμpos)]
    dsimp only [M]
    nlinarith only [mul_le_mul_of_nonneg_right hNOne (inv_nonneg.mpr hμpos.le)]
  have hn1 (i : I) : |coordDeriv i (fun x => (metricDensity g x)⁻¹) y| ≤ M :=
    (hInv.1 i).trans (mul_le_mul_of_nonneg_right hN1 (inv_nonneg.mpr hμpos.le))
  have hn2 (i j : I) : |coordDeriv i (coordDeriv j (fun x => (metricDensity g x)⁻¹)) y| ≤ M :=
    (hInv.2 i j).trans (mul_le_mul_of_nonneg_right hN2 (inv_nonneg.mpr hμpos.le))
  have ha (i j : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix g g₂ r x i j) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hp.1.mul (contDiffOn_principal_entry h h₂ hKpos i j)
  have haAll (i j : I) := scalar_principal_three_jet_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy M1 M2 M3 hM1 hM2 hM3 hD hD2 hD3 i j
  have hProd (i j : I) : CoordinateScalarThreeJetBound
      (fun x => metricDensity g x*scalarPrincipalMatrix g g₂ r x i j) y B :=
    hμAll.mul hY hμ (ha i j) hy (by positivity) (by positivity) (haAll i j)
  constructor
  · intro i k l
    have ht := coordinate_second_adjointFirstCoefficient_bound hY (metricDensity g) (scalarPrincipalMatrix g g₂ r)
      hμ ha hpos hy i k l M B B B hM hn hn1 hn2
      (fun j => (hProd i j).first j) (fun j m => (hProd i j).second m j)
      (fun j m n => (hProd i j).third n m j)
    have hCancel : 6*M*(B+2*B+B) = (192*N*D*A)*ε*β := by
      dsimp only [M,B]
      field_simp [hμpos.ne'] <;> ring
    exact ht.trans_eq hCancel
  · intro k
    have ht := coordinate_adjointZeroCoefficient_bound hY (metricDensity g) (scalarPrincipalMatrix g g₂ r)
      hμ ha hpos hy k M B B hM hn (hn1 k)
      (fun i j => (hProd i j).second j i) (fun i j => (hProd i j).third k j i)
    have hCancel : 9*M*(B+B) = (144*N*D*A)*ε*β := by
      dsimp only [M,B]
      field_simp [hμpos.ne'] <;> ring
    exact ht.trans_eq hCancel

end ShrinkingSpheres
