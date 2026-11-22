module

public import Proof.CalderonN.PolynomialConnection
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

@[expose] public section

/- Port of FischerFields.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finitePolynomialField (b : ι → MvPolynomial (Fin n) ℝ)
    (c : (X n) → ι → ℝ) (x : (X n)) : MvPolynomial (Fin n) ℝ := ∑ i, c x i • b i

def finitePolynomialFieldDerivative (b : ι → MvPolynomial (Fin n) ℝ)
    (c : (X n) → ι → ℝ) (x a : (X n)) : MvPolynomial (Fin n) ℝ :=
  ∑ i, (fderiv ℝ c x a) i • b i

lemma fischerInner_finitePolynomialField (b : ι → MvPolynomial (Fin n) ℝ)
    (d : κ → MvPolynomial (Fin n) ℝ) (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (x : (X n)) :
    fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x) =
      ∑ i, ∑ j, c x i * z x j * fischerInner (b i) (d j) := by
  simp only [finitePolynomialField,fischerInner_sum_left,fischerInner_sum_right,
    smul_eq_C_mul,fischerInner_C_mul_left,fischerInner_C_mul_right,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def polynomialFamilyFischerBilinear (b : ι → MvPolynomial (Fin n) ℝ)
    (d : κ → MvPolynomial (Fin n) ℝ) : (ι → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, fischerInner (b i) (d j) •
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)

lemma polynomialFamilyFischerBilinear_apply (b : ι → MvPolynomial (Fin n) ℝ)
    (d : κ → MvPolynomial (Fin n) ℝ) (c : ι → ℝ) (z : κ → ℝ) :
    polynomialFamilyFischerBilinear b d c z =
      ∑ i, ∑ j, c i * z j * fischerInner (b i) (d j) := by
  simp only [polynomialFamilyFischerBilinear,_root_.sum_apply,
    _root_.smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma fderiv_fischerInner_finitePolynomialField (b : ι → MvPolynomial (Fin n) ℝ)
    (d : κ → MvPolynomial (Fin n) ℝ) (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ)
    (x a : (X n)) (hc : DifferentiableAt ℝ c x) (hz : DifferentiableAt ℝ z x) :
    fderiv ℝ (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) x a =
      fischerInner (finitePolynomialFieldDerivative b c x a) (finitePolynomialField d z x) +
      fischerInner (finitePolynomialField b c x) (finitePolynomialFieldDerivative d z x a) := by
  let B := polynomialFamilyFischerBilinear b d
  have hpair : (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) =
      fun y => B (c y) (z y) := by
    funext y
    rw [fischerInner_finitePolynomialField]
    exact (polynomialFamilyFischerBilinear_apply b d (c y) (z y)).symm
  have hp := ((B.hasFDerivAt.comp x (hc.hasFDerivAt)).clm_apply
    (hz.hasFDerivAt))
  change HasFDerivAt (fun y => B (c y) (z y)) _ x at hp
  rw [hpair,hp.fderiv]
  change B (c x) (fderiv ℝ z x a) + B (fderiv ℝ c x a) (z x) = _
  change B (c x) (fderiv ℝ z x a) + B (fderiv ℝ c x a) (z x) =
    fischerInner (finitePolynomialField b (fun _ => fderiv ℝ c x a) x) (finitePolynomialField d z x) +
    fischerInner (finitePolynomialField b c x) (finitePolynomialField d (fun _ => fderiv ℝ z x a) x)
  simp only [B,polynomialFamilyFischerBilinear_apply,fischerInner_finitePolynomialField]
  exact add_comm _ _


lemma finitePolynomialField_homogeneous {k : ℕ} (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ i, (b i).IsHomogeneous k) (c : (X n) → ι → ℝ) (y : (X n)) :
    (finitePolynomialField b c y).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  simpa only [smul_eq_C_mul] using (hb i).C_mul (c y i)

lemma finitePolynomialField_harmonic (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ i, laplacian (b i) = 0) (c : (X n) → ι → ℝ) (y : (X n)) :
    laplacian (finitePolynomialField b c y) = 0 := by
  simp only [finitePolynomialField, smul_eq_C_mul, laplacian_sum, laplacian_C_mul, hb,
    mul_zero, Finset.sum_const_zero]

/-- Covariant differentiation of a finite polynomial field in frame coordinates. -/
def covariantPolynomialDerivative (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (y a : (X n)) : MvPolynomial (I n) ℝ :=
  finitePolynomialFieldDerivative b c y a +
    polynomialConnectionAction (frameConnectionCoefficient g e y a) (finitePolynomialField b c y)

lemma covariantPolynomialDerivative_fischer_compatible {Ω : Set (X n)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField n)} (h : Elliptic Ω K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Ω)
    (hframe : ∀ x ∈ Ω, ∀ i j, metricPair g x (e x i) (e x j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) {y : (X n)} (hy : y ∈ Ω) (a : (X n))
    (hc : DifferentiableAt ℝ c y) (hz : DifferentiableAt ℝ z y) :
    fderiv ℝ (fun x => fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x)) y a =
      fischerInner (covariantPolynomialDerivative g e b c y a) (finitePolynomialField d z y) +
        fischerInner (finitePolynomialField b c y) (covariantPolynomialDerivative g e d z y a) := by
  rw [fderiv_fischerInner_finitePolynomialField b d c z y a hc hz]
  have hs := actual_polynomialConnection_skew hΩ h hK e he hframe hy a
    (finitePolynomialField b c y) (finitePolynomialField d z y)
  simp only [covariantPolynomialDerivative, fischerInner_add_left, fischerInner_add_right]
  linarith

lemma covariantPolynomialDerivative_homogeneous {k : ℕ} (hk : 1 ≤ k)
    (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (hb : ∀ i, (b i).IsHomogeneous k) (c : (X n) → ι → ℝ) (y a : (X n)) :
    (covariantPolynomialDerivative g e b c y a).IsHomogeneous k := by
  apply MvPolynomial.IsHomogeneous.add
  · exact finitePolynomialField_homogeneous b hb (fun _ => fderiv ℝ c y a) y
  · exact polynomialConnectionAction_homogeneous _ hk _ (finitePolynomialField_homogeneous b hb c y)

lemma covariantPolynomialDerivative_harmonic (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ i, laplacian (b i) = 0) (c : (X n) → ι → ℝ) (y a : (X n))
    (hA : ∀ i j, frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i) :
    laplacian (covariantPolynomialDerivative g e b c y a) = 0 := by
  unfold covariantPolynomialDerivative
  rw [show ∀ p q : MvPolynomial (I n) ℝ, laplacian (p+q) = laplacian p + laplacian q by
    intro p q; simp [laplacian, map_add, Finset.sum_add_distrib]]
  change laplacian (finitePolynomialField b (fun _ => fderiv ℝ c y a) y) +
    laplacian (polynomialConnectionAction (frameConnectionCoefficient g e y a) (finitePolynomialField b c y)) = 0
  rw [finitePolynomialField_harmonic b hb (fun _ => fderiv ℝ c y a) y,
    polynomialConnectionAction_harmonic _ hA _ (finitePolynomialField_harmonic b hb c y), add_zero]

end CalderonN
