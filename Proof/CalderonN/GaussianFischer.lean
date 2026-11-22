module

public import Proof.CalderonN.SphereHarmonicBridge
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

@[expose] public section

/- Port of Proof/Archive/LiteratureGaussianFischer.lean from Proposition 5.3 check
   f308cb9d. The scalar Gaussian identities and finite-product integration are reused. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

variable {n : ℕ}

def gaussPair (p q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∫ x : CalderonN.X n, p.eval (x : Fin n → ℝ) * q.eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2)

lemma integrable_pow_gauss (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) := by
  have hf := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (n : ℝ))
    (by have : (0:ℝ) ≤ n := n.cast_nonneg; linarith)
  refine Integrable.mono' (hf.norm.add hf.comp_neg.norm)
    (by fun_prop : Continuous fun x : ℝ => x ^ n * Real.exp (-x ^ 2)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), neg_mul, one_mul,
    neg_sq]
  simp only [Pi.add_apply]
  have he := Real.exp_pos (-x^2)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (Real.rpow_nonneg hx _), Real.rpow_natCast, abs_of_nonneg hx]
    have := abs_nonneg ((-x) ^ (n:ℝ))
    nlinarith
  · rw [abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ -x) (n:ℝ)), Real.rpow_natCast (-x),
      abs_of_nonpos hx]
    have := abs_nonneg (x ^ (n:ℝ))
    nlinarith

def gaussMoment (n : ℕ) : ℝ := ∫ x : ℝ, x ^ n * Real.exp (-x ^ 2)

lemma gaussMoment_zero : gaussMoment 0 = Real.sqrt Real.pi := by
  have := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at this
  simp [gaussMoment, this]

lemma gaussMoment_succ (n : ℕ) : gaussMoment (n + 1) = (n : ℝ) / 2 * gaussMoment (n - 1) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x ^ n) (u' := fun x => (n : ℝ) * x ^ (n - 1))
    (v := fun x => -(1/2 : ℝ) * Real.exp (-x ^ 2)) (v' := fun x => x * Real.exp (-x ^ 2))
    (fun x _ => by simpa using hasDerivAt_pow n x)
    (fun x _ => by
      have h2 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
        simpa using (hasDerivAt_pow 2 x).fun_neg
      have := (h2.exp).const_mul (-(1/2 : ℝ))
      convert this using 1; ring)
    (by
      refine (integrable_pow_gauss (n + 1)).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      refine ((integrable_pow_gauss (n - 1)).const_mul (-(n : ℝ) / 2)).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      refine ((integrable_pow_gauss n).const_mul (-(1/2 : ℝ))).congr
        (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
  have e1 : (fun x : ℝ => x ^ n * (x * Real.exp (-x ^ 2))) =
      fun x => x ^ (n + 1) * Real.exp (-x ^ 2) := by ext x; ring
  have e2 : (fun x : ℝ => (n : ℝ) * x ^ (n - 1) * (-(1/2 : ℝ) * Real.exp (-x ^ 2))) =
      fun x => (-(n : ℝ) / 2) * (x ^ (n - 1) * Real.exp (-x ^ 2)) := by ext x; ring
  rw [e1, e2, integral_const_mul] at h
  rw [gaussMoment, h, gaussMoment]; ring

lemma monomial_gauss_eq (a : Fin n →₀ ℕ) (c : ℝ) :
    (fun x : CalderonN.X n => (monomial a c).eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2)) =
      (fun y : Fin n → ℝ => c * ∏ i, (y i ^ a i * Real.exp (-(y i) ^ 2))) ∘
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm := by
  ext x
  simp only [Function.comp_apply, eval_monomial, EuclideanSpace.real_norm_sq_eq,
    Finset.prod_mul_distrib]
  rw [Finsupp.prod_fintype _ _ (by simp), ← Finset.sum_neg_distrib, Real.exp_sum]
  simp [mul_assoc]

lemma integrable_monomial_gauss (a : Fin n →₀ ℕ) (c : ℝ) :
    Integrable (fun x : CalderonN.X n => (monomial a c).eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2)) := by
  rw [monomial_gauss_eq, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin n)).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  exact (Integrable.fintype_prod (f := fun i (t : ℝ) => t ^ a i * Real.exp (-t ^ 2))
    (fun i => integrable_pow_gauss (a i))).const_mul c

lemma integral_monomial_gauss (a : Fin n →₀ ℕ) (c : ℝ) :
    ∫ x : CalderonN.X n, (monomial a c).eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2) =
      c * ∏ i, gaussMoment (a i) := by
  rw [monomial_gauss_eq]
  refine ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin n)).integral_comp'
      (fun y : Fin n → ℝ => c * ∏ i, (y i ^ a i * Real.exp (-(y i) ^ 2)))).trans ?_
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_volume_eq_prod (f := fun i (t : ℝ) => t ^ a i * Real.exp (-t ^ 2))

lemma integrable_poly_gauss (f : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x : CalderonN.X n => f.eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2)) := by
  induction f using MvPolynomial.induction_on' with
  | monomial a c => exact integrable_monomial_gauss a c
  | add p q hp hq => convert hp.add hq using 1; ext x; simp [add_mul]

def gaussFunctional : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun f := ∫ x : CalderonN.X n, f.eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2)
  map_add' p q := by
    rw [← integral_add (integrable_poly_gauss p) (integrable_poly_gauss q)]
    congr 1; ext x; simp [add_mul]
  map_smul' c p := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    congr 1; ext x; simp [mul_assoc]

lemma gaussFunctional_apply (f : MvPolynomial (Fin n) ℝ) :
    gaussFunctional f = ∫ x : CalderonN.X n, f.eval (x : Fin n → ℝ) * Real.exp (-‖x‖ ^ 2) := rfl

lemma gaussFunctional_monomial (a : Fin n →₀ ℕ) (c : ℝ) :
    gaussFunctional (monomial a c) = c * ∏ i, gaussMoment (a i) :=
  integral_monomial_gauss a c

lemma gaussFunctional_X_mul (i : Fin n) (g : MvPolynomial (Fin n) ℝ) :
    gaussFunctional (X i * g) = 1 / 2 * gaussFunctional (pderiv i g) := by
  induction g using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial a c =>
    rw [X, monomial_mul_monomial, pderiv_monomial, gaussFunctional_monomial,
      gaussFunctional_monomial, one_mul,
      Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
    have h1 : ∀ j ∈ ({i}ᶜ : Finset (Fin n)),
        gaussMoment ((Finsupp.single i 1 + a : Fin n →₀ ℕ) j) = gaussMoment (a j) := by
      intro j hj
      rw [Finset.mem_compl, Finset.mem_singleton] at hj
      simp [Ne.symm hj]
    have h2 : ∀ j ∈ ({i}ᶜ : Finset (Fin n)),
        gaussMoment ((a - Finsupp.single i 1 : Fin n →₀ ℕ) j) = gaussMoment (a j) := by
      intro j hj
      rw [Finset.mem_compl, Finset.mem_singleton] at hj
      simp [Ne.symm hj]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.coe_tsub,
      Pi.sub_apply]
    rw [add_comm 1, gaussMoment_succ]
    ring

lemma pderiv_mem_harmonic {k : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneous n k) (i : Fin n) :
    pderiv i p ∈ harmonicHomogeneous n (k - 1) := by
  refine ⟨hp.1.pderiv, ?_⟩
  rw [laplacian_pderiv, hp.2, map_zero]

lemma gaussPair_eq_gaussFunctional (p q : MvPolynomial (Fin n) ℝ) :
    gaussPair p q = gaussFunctional (p * q) := by
  simp [gaussPair, gaussFunctional_apply]

lemma gaussPair_comm (p q : MvPolynomial (Fin n) ℝ) : gaussPair p q = gaussPair q p := by
  rw [gaussPair_eq_gaussFunctional, gaussPair_eq_gaussFunctional, mul_comm]

lemma gaussPair_rec {k : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ harmonicHomogeneous n k)
    (q : MvPolynomial (Fin n) ℝ) :
    (k : ℝ) * gaussPair p q = 1 / 2 * ∑ i, gaussPair (pderiv i p) (pderiv i q) := by
  have hE := hp.1.sum_X_mul_pderiv
  have hΔ : ∑ i, pderiv i (pderiv i p) = 0 := hp.2
  have : (k : ℝ) * gaussPair p q = ∑ i, gaussFunctional (X i * (pderiv i p * q)) := by
    rw [gaussPair_eq_gaussFunctional, ← map_sum]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hE, smul_mul_assoc, map_nsmul, nsmul_eq_mul]
  rw [this]
  simp_rw [gaussFunctional_X_mul, Derivation.leibniz, smul_eq_mul, map_add, ← Finset.mul_sum,
    Finset.sum_add_distrib, gaussPair_eq_gaussFunctional]
  have h0 : ∑ x, gaussFunctional (q * pderiv x (pderiv x p)) = 0 := by
    rw [← map_sum, ← Finset.mul_sum, hΔ, mul_zero, map_zero]
  rw [h0, add_zero]

lemma fischerInner_eq_sum (p q : MvPolynomial (Fin n) ℝ) :
    fischerInner p q = ∑ a ∈ p.support, p.coeff a * q.coeff a * fischerWeight a := by
  rw [fischerInner, sum_def]

lemma fischerWeight_add_single (a : Fin n →₀ ℕ) (i : Fin n) :
    fischerWeight (a + Finsupp.single i 1) = ((a i : ℝ) + 1) * fischerWeight a := by
  unfold fischerWeight
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have h : ∀ j ∈ ({i}ᶜ : Finset (Fin n)),
      ((Nat.factorial ((a + Finsupp.single i 1 : Fin n →₀ ℕ) j) : ℕ) : ℝ) =
        (Nat.factorial (a j) : ℝ) := by
    intro j hj
    rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp [Ne.symm hj]
  rw [Finset.prod_congr rfl h]
  simp [Nat.factorial_succ]
  ring

lemma fischerInner_pderiv (i : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    fischerInner (pderiv i p) (pderiv i q) =
      ∑ b ∈ p.support, (b i : ℝ) * (p.coeff b * q.coeff b * fischerWeight b) := by
  have key : ∀ a : Fin n →₀ ℕ,
      (pderiv i p).coeff a * (pderiv i q).coeff a * fischerWeight a =
        ((a + Finsupp.single i 1 : Fin n →₀ ℕ) i : ℝ) *
          (p.coeff (a + Finsupp.single i 1) * q.coeff (a + Finsupp.single i 1) *
            fischerWeight (a + Finsupp.single i 1)) := by
    intro a
    rw [coeff_pderiv, coeff_pderiv, fischerWeight_add_single]
    simp
    ring
  rw [fischerInner_eq_sum]
  refine Finset.sum_bij_ne_zero (fun a _ _ => a + Finsupp.single i 1) ?_ ?_ ?_ ?_
  · intro a ha _
    rw [mem_support_iff, coeff_pderiv] at ha
    exact mem_support_iff.mpr (left_ne_zero_of_mul ha)
  · intro a _ _ b _ _ h
    exact add_right_cancel h
  · intro b hb hne
    have hbi : b i ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have hle : Finsupp.single i 1 ≤ b := by
      rw [Finsupp.single_le_iff]; omega
    have hab : b - Finsupp.single i 1 + Finsupp.single i 1 = b := tsub_add_cancel_of_le hle
    refine ⟨b - Finsupp.single i 1, ?_, ?_, hab⟩
    · rw [mem_support_iff, coeff_pderiv, hab]
      exact mul_ne_zero (mem_support_iff.mp hb) (by positivity)
    · rw [key, hab]; exact hne
  · intro a _ _
    exact key a

lemma sum_fischerInner_pderiv {k : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous k)
    (q : MvPolynomial (Fin n) ℝ) :
    ∑ i, fischerInner (pderiv i p) (pderiv i q) = (k : ℝ) * fischerInner p q := by
  simp_rw [fischerInner_pderiv]
  rw [Finset.sum_comm, fischerInner_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [hp.degree_eq_sum_deg_support hb, Nat.cast_sum]
  exact (Finset.sum_subset (Finset.subset_univ _) (by simp_all)).symm

lemma gaussPair_C_C (n : ℕ) (a b : ℝ) :
    gaussPair (C a : MvPolynomial (Fin n) ℝ) (C b) = Real.pi ^ ((n : ℝ) / 2) * (a * b) := by
  rw [gaussPair_eq_gaussFunctional, ← C_mul, ← monomial_zero', gaussFunctional_monomial]
  simp only [Finsupp.coe_zero, Pi.zero_apply, gaussMoment_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
  ring

lemma eq_C_of_mem_harmonicHomogeneous_zero {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneous n 0) :
    p = C (p.coeff 0) :=
  totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (p := p)).mpr hp.1)

lemma fischerInner_C_C (n : ℕ) (a b : ℝ) : fischerInner (C a : MvPolynomial (Fin n) ℝ) (C b) = a * b := by
  rw [fischerInner, sum_C (by simp)]
  simp [fischerWeight]

lemma gaussPair_eq_zero_of_lt {m k : ℕ} (hmk : m < k) {p q : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneous n k) (hq : q ∈ harmonicHomogeneous n m) : gaussPair p q = 0 := by
  induction m generalizing k p q with
  | zero =>
    have h := gaussPair_rec hp q
    rw [eq_C_of_mem_harmonicHomogeneous_zero hq] at h ⊢
    simp only [pderiv_C, gaussPair_eq_gaussFunctional, mul_zero, map_zero,
      Finset.sum_const_zero] at h
    rw [gaussPair_eq_gaussFunctional]
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hmk.ne'
    exact (mul_eq_zero.mp h).resolve_left hk
  | succ m ih =>
    have h := gaussPair_rec hp q
    have hz : ∀ i, gaussPair (pderiv i p) (pderiv i q) = 0 := fun i =>
      ih (by omega) (pderiv_mem_harmonic hp i) (pderiv_mem_harmonic hq i)
    simp only [hz, Finset.sum_const_zero, mul_zero] at h
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    exact (mul_eq_zero.mp h).resolve_left hk

theorem gaussPair_eq_zero {k m : ℕ} (hkm : k ≠ m) {p q : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneous n k) (hq : q ∈ harmonicHomogeneous n m) : gaussPair p q = 0 := by
  rcases Nat.lt_or_gt_of_ne hkm with h | h
  · rw [gaussPair_comm]; exact gaussPair_eq_zero_of_lt h hq hp
  · exact gaussPair_eq_zero_of_lt h hp hq

theorem gaussPair_eq_fischer {k : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ harmonicHomogeneous n k) (hq : q ∈ harmonicHomogeneous n k) :
    gaussPair p q = Real.pi ^ ((n : ℝ) / 2) / 2 ^ k * fischerInner p q := by
  induction k generalizing p q with
  | zero =>
    rw [eq_C_of_mem_harmonicHomogeneous_zero hp, eq_C_of_mem_harmonicHomogeneous_zero hq,
      gaussPair_C_C, fischerInner_C_C]
    simp
  | succ k ih =>
    have h := gaussPair_rec hp q
    have hi : ∀ i, gaussPair (pderiv i p) (pderiv i q) =
        Real.pi ^ ((n : ℝ) / 2) / 2 ^ k * fischerInner (pderiv i p) (pderiv i q) := fun i =>
      ih (pderiv_mem_harmonic hp i) (pderiv_mem_harmonic hq i)
    simp only [hi] at h
    rw [← Finset.mul_sum, sum_fischerInner_pderiv hp.1] at h
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    apply mul_left_cancel₀ hk
    rw [h, pow_succ]
    field_simp

end OAI.AnisotropicCalderon.SphereHarmonic
