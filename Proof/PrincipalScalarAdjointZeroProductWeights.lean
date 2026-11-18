import Proof.LocalScalarAdjointSmoothness
import Proof.PrincipalAdjointHigherWeights
import Proof.PrincipalAdjointWeights
import Proof.ScalarPrincipalSharpTwoJets
import Proof.Archive.ScalarSelfFormBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

def scalarAdjointZeroProductWeight (g g₂ : MetricField) (r : X → ℝ) (i j : I) (x : X) : ℝ :=
  metricDensity g x*scalarPrincipalMatrix g g₂ r x i j*
    adjointZeroCoefficient axis (metricDensity g) (scalarPrincipalMatrix g g₂ r) x

def scalarAdjointZeroProductValueBudget (K M1 M2 C2 : ℝ) : ℝ :=
  principalZeroBudget K*|principalAdjointZeroBudget K M1 M2 C2|

def scalarAdjointZeroProductFirstBudget (K M1 M2 M3 C2 C3 : ℝ) : ℝ :=
  principalDensityProductFirstBudget K M1*|principalAdjointZeroBudget K M1 M2 C2|+
    principalZeroBudget K*|principalAdjointZeroFirstWeightBudget K M1 M2 M3 C2 C3|

lemma scalarAdjointZeroProductBudgets_nonneg (K M1 M2 M3 C2 C3 : ℝ)
    (hK : 0 ≤ K) (hM1 : 0 ≤ M1) :
    0 ≤ scalarAdjointZeroProductValueBudget K M1 M2 C2 ∧
      0 ≤ scalarAdjointZeroProductFirstBudget K M1 M2 M3 C2 C3 := by
  dsimp only [scalarAdjointZeroProductValueBudget,scalarAdjointZeroProductFirstBudget,
    principalDensityProductFirstBudget,principalZeroBudget,principalFirstBudget,densityFirstBudget]
  constructor <;> positivity

lemma scalarAdjointZeroProductWeight_smooth {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g g₂ : MetricField} (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂)
    (hK : 0 < K) (r : X → ℝ) (hr : ContDiffOn ℝ ∞ r Y) (i j : I) :
    ContDiffOn ℝ ∞ (scalarAdjointZeroProductWeight g g₂ r i j) Y := by
  have hmu := h.contDiffOn_density hK
  have ha (a b : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix g g₂ r x a b) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hr.mul (contDiffOn_principal_entry h h₂ hK a b)
  have hC := contDiffOn_adjointZeroCoefficient hY (metricDensity g) (scalarPrincipalMatrix g g₂ r)
    hmu ha (fun x hx => (metricDensity_pos h hK hx).ne')
  exact (hmu.mul (ha i j)).mul hC

/-- SAME density*rP*scalar-adjoint-zero product has epsilon-squared over
beta squared/first weights. The supplied common product estimate is used
with the beta scale of the zero adjoint coefficient. -/
theorem scalar_principal_adjoint_zero_product_weights {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g g₂ : MetricField} (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K)
    (e : Frame) (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2)
    (hD3 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x a b))) y‖ ≤ M3) (i j : I) :
    |scalarAdjointZeroProductWeight g g₂ r i j y| ≤
      metricDensity g y*scalarAdjointZeroProductValueBudget K M1 M2 (Cj 2)*ε^2/(beta g r y)^2 ∧
    ∀ k : I,|coordDeriv k (scalarAdjointZeroProductWeight g g₂ r i j) y| ≤
      metricDensity g y*scalarAdjointZeroProductFirstBudget K M1 M2 M3 (Cj 2) (Cj 3)*ε^2/beta g r y := by
  let μ := metricDensity g
  let A := scalarPrincipalMatrix g g₂ r
  let c := adjointZeroCoefficient axis μ A
  let β := beta g r y
  let t := β⁻¹
  let A0 := principalZeroBudget K
  let E1 := principalDensityProductFirstBudget K M1
  let Z := |principalAdjointZeroBudget K M1 M2 (Cj 2)|
  let Zd := |principalAdjointZeroFirstWeightBudget K M1 M2 M3 (Cj 2) (Cj 3)|
  have hKpos := zero_lt_one.trans_le hK
  have hK0 := zero_le_one.trans hK
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβpos := zero_lt_one.trans_le hβ
  have hμ : 0 ≤ μ y := Real.sqrt_nonneg _
  have hA00 : 0 ≤ A0 := by dsimp only [A0,principalZeroBudget];positivity
  have hE10 : 0 ≤ E1 := by dsimp only [E1,principalDensityProductFirstBudget,densityFirstBudget,
    principalZeroBudget,principalFirstBudget];positivity
  have hZ : 0 ≤ Z := abs_nonneg _
  have hZd : 0 ≤ Zd := abs_nonneg _
  have hA0 : |A y i j| ≤ A0*ε/β^2 :=
    (scalar_principal_sharp_two_jet_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy
      M1 M2 hM1 hM2 hD hD2 i j 0 0).1
  have hc0 : |c y| ≤ Z*ε :=
    (scalar_principal_adjoint_coefficient_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy
      M1 M2 hM1 hM2 hD hD2).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
  have hμA : |μ y*A y i j| ≤ μ y*A0*ε/β^2 := by
    rw [abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left hA0 hμ).trans_eq (by ring)
  constructor
  · change |(μ y*A y i j)*c y| ≤ _
    rw [abs_mul]
    apply (mul_le_mul hμA hc0 (abs_nonneg _) (by positivity)).trans_eq
    dsimp only [scalarAdjointZeroProductValueBudget,A0,Z,β]
    field_simp
    ring
  · intro k
    have hmuS := h.contDiffOn_density hKpos
    have haS (a b : I) : ContDiffOn ℝ ∞ (fun x => A x a b) Y := by
      simpa only [A,scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using
        hp.1.mul (contDiffOn_principal_entry h h₂ hKpos a b)
    have hcS : ContDiffOn ℝ ∞ c Y := contDiffOn_adjointZeroCoefficient hY μ A hmuS haS
      (fun x hx => (metricDensity_pos h hKpos hx).ne')
    have hDμA : |coordDeriv k (fun x => μ x*A x i j) y| ≤ μ y*E1*ε/β :=
      (scalar_principal_density_product_two_jets hY h h₂ hK e hframe hp hf hε hε1 hs hy
        M1 M2 hM1 hM2 hD hD2 i j k k).1
    have hDc : |coordDeriv k c y| ≤ Zd*ε*β :=
      (scalar_principal_adjoint_higher_coefficient_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy
        M1 M2 M3 hM1 hM2 hM3 hD hD2 hD3).2 k |>.trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε) hβpos.le)
    have hFormula : coordDeriv k (scalarAdjointZeroProductWeight g g₂ r i j) y=
        coordDeriv k (fun x => μ x*A x i j) y*c y+μ y*A y i j*coordDeriv k c y :=
      coordinate_mul hY (hmuS.mul (haS i j)) hcS hy k
    rw [hFormula]
    have hAt : |μ y*A y i j| ≤ (μ y*A0)*ε*t^2 := by
      simpa only [t,div_eq_mul_inv,inv_pow,mul_assoc] using hμA
    have hDAt : |coordDeriv k (fun x => μ x*A x i j) y| ≤ (μ y*E1)*ε*t := by
      simpa only [t,div_eq_mul_inv,mul_assoc] using hDμA
    have hCt : |c y| ≤ (Z*β)*ε*t := hc0.trans_eq (by dsimp only [t];field_simp <;> ring)
    have hDCt : |coordDeriv k c y| ≤ (Zd*β)*ε := hDc.trans_eq (by ring)
    have ht := OAI.AnisotropicCalderon.ActualScalarPrincipalSelfFormBound.abs_ab_product_derivative_le
      1 0 (μ y*A y i j) (coordDeriv k (fun x => μ x*A x i j) y) (c y) (coordDeriv k c y)
      0 (μ y*A0) (μ y*E1) (Z*β) (Zd*β) ε t (by norm_num) (by norm_num)
      (mul_nonneg hμ hA00) (mul_nonneg hμ hE10) (mul_nonneg hZ hβpos.le) (mul_nonneg hZd hβpos.le)
      hε (inv_nonneg.mpr hβpos.le) ((inv_le_one₀ hβpos).mpr hβ) (by norm_num) hAt hDAt hCt hDCt
    simp only [zero_mul,one_mul,zero_add] at ht
    apply ht.trans_eq
    dsimp only [t,scalarAdjointZeroProductFirstBudget,E1,A0,Z,Zd,β]
    field_simp
    ring

end ShrinkingSpheres
