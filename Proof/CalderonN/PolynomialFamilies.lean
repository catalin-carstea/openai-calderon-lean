module

public import Proof.CalderonN.EvaluatedFields
import Mathlib.Tactic

@[expose] public section

/- Port of PolynomialFamilies.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}
variable [NeZero n]

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma finitePolynomialField_coeff_smul (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ)
    (a : (X n) → ℝ) (y : (X n)) :
    finitePolynomialField b (fun x => a x • c x) y = a y • finitePolynomialField b c y := by
  simp only [finitePolynomialField, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

lemma covariantPolynomialDerivative_coeff_smul (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (a : (X n) → ℝ) (y v : (X n))
    (hc : DifferentiableAt ℝ c y) (ha : DifferentiableAt ℝ a y) :
    covariantPolynomialDerivative g e b (fun x => a x • c x) y v =
      C (a y) * covariantPolynomialDerivative g e b c y v +
      C (fderiv ℝ a y v) * finitePolynomialField b c y := by
  have hd : finitePolynomialFieldDerivative b (fun x => a x • c x) y v =
      a y • finitePolynomialFieldDerivative b c y v +
      (fderiv ℝ a y v) • finitePolynomialField b c y := by
    simp only [finitePolynomialFieldDerivative, finitePolynomialField, fderiv_fun_smul ha hc,
      _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, smul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  have hA : polynomialConnectionAction (frameConnectionCoefficient g e y v)
      (a y • finitePolynomialField b c y) =
      a y • polynomialConnectionAction (frameConnectionCoefficient g e y v) (finitePolynomialField b c y) :=
    (polynomialConnectionLinear (frameConnectionCoefficient g e y v)).map_smul _ _
  rw [covariantPolynomialDerivative, hd, finitePolynomialField_coeff_smul, hA]
  simp only [covariantPolynomialDerivative, ← smul_eq_C_mul, smul_add]
  abel

def joinedPolynomialFamily (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ) :
    ι ⊕ κ → MvPolynomial (I n) ℝ := Sum.elim b d

def joinedCoefficientFamily (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (x : (X n)) : ι ⊕ κ → ℝ :=
  Sum.elim (c x) (z x)

lemma contDiffOn_joinedCoefficientFamily {Ω : Set (X n)} (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ)
    (hc : ContDiffOn ℝ ∞ c Ω) (hz : ContDiffOn ℝ ∞ z Ω) :
    ContDiffOn ℝ ∞ (joinedCoefficientFamily c z) Ω := by
  apply contDiffOn_pi.mpr
  intro a
  cases a with
  | inl i => exact contDiffOn_pi.mp hc i
  | inr j => exact contDiffOn_pi.mp hz j

lemma finitePolynomialField_joined (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (y : (X n)) :
    finitePolynomialField (joinedPolynomialFamily b d) (joinedCoefficientFamily c z) y =
      finitePolynomialField b c y + finitePolynomialField d z y := by
  simp only [finitePolynomialField, Fintype.sum_sum_type, joinedPolynomialFamily,
    joinedCoefficientFamily, Sum.elim_inl, Sum.elim_inr]

lemma covariantPolynomialDerivative_joined (g : (MetricField n)) (e : (Frame n))
    (b : ι → MvPolynomial (I n) ℝ) (d : κ → MvPolynomial (I n) ℝ)
    (c : (X n) → ι → ℝ) (z : (X n) → κ → ℝ) (y v : (X n))
    (hc : DifferentiableAt ℝ c y) (hz : DifferentiableAt ℝ z y) :
    covariantPolynomialDerivative g e (joinedPolynomialFamily b d) (joinedCoefficientFamily c z) y v =
      covariantPolynomialDerivative g e b c y v + covariantPolynomialDerivative g e d z y v := by
  have hjoin : DifferentiableAt ℝ (joinedCoefficientFamily c z) y := by
    apply differentiableAt_pi.mpr
    intro a
    cases a with
    | inl i => exact differentiableAt_pi.mp hc i
    | inr j => exact differentiableAt_pi.mp hz j
  have hleft (a : ι) : fderiv ℝ (joinedCoefficientFamily c z) y v (.inl a) = fderiv ℝ c y v a := by
    have hh := congrArg (fun T : (X n) →L[ℝ] ℝ => T v) (fderiv_apply hjoin (.inl a))
    change fderiv ℝ (fun x => c x a) y v = _ at hh
    rw [fderiv_apply hc a] at hh
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hh.symm
  have hright (a : κ) : fderiv ℝ (joinedCoefficientFamily c z) y v (.inr a) = fderiv ℝ z y v a := by
    have hh := congrArg (fun T : (X n) →L[ℝ] ℝ => T v) (fderiv_apply hjoin (.inr a))
    change fderiv ℝ (fun x => z x a) y v = _ at hh
    rw [fderiv_apply hz a] at hh
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hh.symm
  have hd : finitePolynomialFieldDerivative (joinedPolynomialFamily b d) (joinedCoefficientFamily c z) y v =
      finitePolynomialFieldDerivative b c y v + finitePolynomialFieldDerivative d z y v := by
    simp only [finitePolynomialFieldDerivative, Fintype.sum_sum_type, joinedPolynomialFamily,
      Sum.elim_inl, Sum.elim_inr, hleft, hright]
  have hA : polynomialConnectionAction (frameConnectionCoefficient g e y v)
      (finitePolynomialField b c y + finitePolynomialField d z y) =
      polynomialConnectionAction (frameConnectionCoefficient g e y v) (finitePolynomialField b c y) +
      polynomialConnectionAction (frameConnectionCoefficient g e y v) (finitePolynomialField d z y) :=
    (polynomialConnectionLinear (frameConnectionCoefficient g e y v)).map_add _ _
  simp only [covariantPolynomialDerivative, hd, finitePolynomialField_joined, hA]
  abel

end CalderonN
