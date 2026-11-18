import Proof.LocalScalarAdjointSmoothness
import Proof.PrincipalAdjointFirstWeight
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

def scalarAdjointProductWeight (g g₂ : MetricField) (r : X → ℝ) (i j l : I) (x : X) : ℝ :=
  metricDensity g x*scalarPrincipalMatrix g g₂ r x i j*
    adjointFirstCoefficient axis (metricDensity g) (scalarPrincipalMatrix g g₂ r) x l

def scalarAdjointProductZeroBudget (K M1 : ℝ) : ℝ :=
  principalZeroBudget K*principalAdjointFirstBudget K M1

def scalarAdjointProductFirstBudget (K M1 M2 C2 : ℝ) : ℝ :=
  principalDensityProductFirstBudget K M1*principalAdjointFirstBudget K M1+
    principalZeroBudget K*principalAdjointFirstDerivativeBudget K M1 M2 C2

lemma scalarAdjointProductBudgets_nonneg (K M1 M2 C2 : ℝ)
    (hK : 0 ≤ K) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) :
    0 ≤ scalarAdjointProductZeroBudget K M1 ∧ 0 ≤ scalarAdjointProductFirstBudget K M1 M2 C2 := by
  dsimp only [scalarAdjointProductZeroBudget,scalarAdjointProductFirstBudget,
    principalAdjointFirstDerivativeBudget,principalDensityProductFirstBudget,principalDensityProductSecondBudget,
    principalAdjointFirstBudget,principalZeroBudget,principalFirstBudget,principalSecondBudget,
    densityFirstBudget,densitySecondBudget]
  constructor <;> positivity

lemma scalarAdjointProductWeight_smooth {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g g₂ : MetricField} (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂)
    (hK : 0 < K) (r : X → ℝ) (hr : ContDiffOn ℝ ∞ r Y) (i j l : I) :
    ContDiffOn ℝ ∞ (scalarAdjointProductWeight g g₂ r i j l) Y := by
  have hmu := h.contDiffOn_density hK
  have ha (a b : I) : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix g g₂ r x a b) Y := by
    simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using hr.mul (contDiffOn_principal_entry h h₂ hK a b)
  have hB := contDiffOn_adjointFirstCoefficient hY (metricDensity g) (scalarPrincipalMatrix g g₂ r)
    hmu ha (fun x hx => (metricDensity_pos h hK hx).ne') l
  exact (hmu.mul (ha i j)).mul hB

/-- SAME actual scalar principal/adjoint product in the third-base form:
its zero and first weights are epsilon squared over beta cubed/squared.
The existing actual density and scalar-adjoint producers are reused. -/
theorem scalar_principal_adjoint_product_weights {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M1)
    (hD2 : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M2) (i j l : I) :
    |scalarAdjointProductWeight g g₂ r i j l y| ≤
      metricDensity g y*scalarAdjointProductZeroBudget K M1*ε^2/(beta g r y)^3 ∧
    ∀ k : I,|coordDeriv k (scalarAdjointProductWeight g g₂ r i j l) y| ≤
      metricDensity g y*scalarAdjointProductFirstBudget K M1 M2 (Cj 2)*ε^2/(beta g r y)^2 := by
  let μ := metricDensity g
  let A := scalarPrincipalMatrix g g₂ r
  let b := fun x => adjointFirstCoefficient axis μ A x l
  let β := beta g r y
  let A0 := principalZeroBudget K
  let B := principalAdjointFirstBudget K M1
  let E1 := principalDensityProductFirstBudget K M1
  let Bd := principalAdjointFirstDerivativeBudget K M1 M2 (Cj 2)
  have hKpos := zero_lt_one.trans_le hK
  have hK0 := zero_le_one.trans hK
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβpos := zero_lt_one.trans_le hβ
  have hμ : 0 ≤ μ y := Real.sqrt_nonneg _
  have hPos : 0 ≤ A0 ∧ 0 ≤ B ∧ 0 ≤ E1 ∧ 0 ≤ Bd := by
    dsimp only [A0,B,E1,Bd,principalZeroBudget,principalAdjointFirstBudget,
      principalDensityProductFirstBudget,principalAdjointFirstDerivativeBudget,principalDensityProductSecondBudget,
      densityFirstBudget,densitySecondBudget,principalFirstBudget,principalSecondBudget]
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  obtain ⟨hA00,hB00,hE10,hBd0⟩ := hPos
  have hA0 : |A y i j| ≤ A0*ε/β^2 :=
    (scalar_principal_sharp_two_jet_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy
      M1 M2 hM1 hM2 hD hD2 i j 0 0).1
  have hB0 : |b y| ≤ B*ε/β :=
    (scalar_principal_adjoint_coefficient_weights hY h h₂ hK e hframe hp hf hε hε1 hs hy
      M1 M2 hM1 hM2 hD hD2).1 l
  have hμA : |μ y*A y i j| ≤ μ y*A0*ε/β^2 := by
    rw [abs_mul,abs_of_nonneg hμ]
    exact (mul_le_mul_of_nonneg_left hA0 hμ).trans_eq (by ring)
  constructor
  · change |(μ y*A y i j)*b y| ≤ _
    rw [abs_mul]
    apply (mul_le_mul hμA hB0 (abs_nonneg _) (by positivity)).trans_eq
    dsimp only [scalarAdjointProductZeroBudget,A0,B,β]
    field_simp
    ring
  · intro k
    have hmuS := h.contDiffOn_density hKpos
    have haS (a b : I) : ContDiffOn ℝ ∞ (fun x => A x a b) Y := by
      simpa only [A,scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using
        hp.1.mul (contDiffOn_principal_entry h h₂ hKpos a b)
    have hbS : ContDiffOn ℝ ∞ b Y := contDiffOn_adjointFirstCoefficient hY μ A hmuS haS
      (fun x hx => (metricDensity_pos h hKpos hx).ne') l
    have hDμA : |coordDeriv k (fun x => μ x*A x i j) y| ≤ μ y*E1*ε/β :=
      (scalar_principal_density_product_two_jets hY h h₂ hK e hframe hp hf hε hε1 hs hy
        M1 M2 hM1 hM2 hD hD2 i j k k).1
    have hDb : |coordDeriv k b y| ≤ Bd*ε :=
      scalar_principal_adjoint_first_derivative_weight hY h h₂ hK e hframe hp hf hε hε1 hs hy
        M1 M2 hM1 hM2 hD hD2 l k
    have hFormula : coordDeriv k (scalarAdjointProductWeight g g₂ r i j l) y=
        coordDeriv k (fun x => μ x*A x i j) y*b y+μ y*A y i j*coordDeriv k b y := by
      exact coordinate_mul hY (hmuS.mul (haS i j)) hbS hy k
    rw [hFormula]
    let t := β⁻¹
    have hAt : |μ y*A y i j| ≤ (μ y*A0)*ε*t^2 := by
      simpa only [t,div_eq_mul_inv,inv_pow,mul_assoc] using hμA
    have hDAt : |coordDeriv k (fun x => μ x*A x i j) y| ≤ (μ y*E1)*ε*t := by
      simpa only [t,div_eq_mul_inv,mul_assoc] using hDμA
    have hBt : |b y| ≤ B*ε*t := by simpa only [t,div_eq_mul_inv] using hB0
    have ht := OAI.AnisotropicCalderon.ActualScalarPrincipalSelfFormBound.abs_ab_product_derivative_le
      1 0 (μ y*A y i j) (coordDeriv k (fun x => μ x*A x i j) y) (b y) (coordDeriv k b y)
      0 (μ y*A0) (μ y*E1) B Bd ε t (by norm_num) (by norm_num)
      (mul_nonneg hμ hA00) (mul_nonneg hμ hE10) hB00 hBd0 hε
      (inv_nonneg.mpr hβpos.le) ((inv_le_one₀ hβpos).mpr hβ) (by norm_num) hAt hDAt hBt hDb
    simp only [zero_mul,one_mul,zero_add] at ht
    apply ht.trans_eq
    dsimp only [t,scalarAdjointProductFirstBudget,E1,B,A0,Bd,β]
    field_simp
    ring

end ShrinkingSpheres
