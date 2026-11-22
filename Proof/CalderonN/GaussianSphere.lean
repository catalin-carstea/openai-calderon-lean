module

public import Proof.CalderonN.GaussianFischer
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

@[expose] public section

/- Port of the Gaussian radial comparison and sphere pairing from Proposition 5.3
   check f308cb9d, Archive/Literature{GaussianSphere,SphereIntegrals,SphereFischerInner}. -/
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace ENNReal

namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

variable {n : ℕ}

/-- Use the same unnormalized Haar sphere measure as the protected probability measure. -/
def surfaceMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (CalderonN.X n)).toSphere

instance (n : ℕ) : IsFiniteMeasure (surfaceMeasure n) := by
  change IsFiniteMeasure ((volume : Measure (CalderonN.X n)).toSphere)
  infer_instance

open Set in
 
lemma radial_gamma (d q : ℕ) :
    ∫ r : Ioi (0:ℝ), r.1 ^ d * Real.exp (-r.1 ^ 2) ∂(Measure.volumeIoiPow q) =
      Real.Gamma (((d : ℝ) + q + 1) / 2) / 2 := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (measurable_subtype_coe.pow_const _).real_toNNReal,
    integral_subtype_comap measurableSet_Ioi
      (fun a : ℝ ↦ Real.toNNReal (a ^ q) • (a ^ d * Real.exp (-a ^ 2)))]
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (d:ℝ) + q) two_pos
    (by linarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) q])
  rw [div_eq_inv_mul, ← one_div, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx : (0:ℝ) < x := hx
  rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul,
    Real.rpow_add hx, Real.rpow_natCast, Real.rpow_natCast]
  rw [← mul_assoc, mul_comm (x ^ q) (x ^ d), Real.rpow_two]

 

variable [NeZero n]

theorem integral_mul_gaussian_of_homogeneous {f : (CalderonN.X n) → ℝ} (d : ℕ)
    (hhom : ∀ (t : ℝ) (x : (CalderonN.X n)), 0 < t → f (t • x) = t ^ d * f x) :
    ∫ x : (CalderonN.X n), f x * Real.exp (-‖x‖ ^ 2) =
      (∫ ω : UnitSphere n, f ω ∂surfaceMeasure n) * (Real.Gamma (((d : ℝ)+n)/2) / 2) := by
  set g : (CalderonN.X n) → ℝ := fun x ↦ f x * Real.exp (-‖x‖ ^ 2) with hg
  have hdim : Module.finrank ℝ (CalderonN.X n) - 1 = n-1 := by rw [finrank_euclideanSpace_fin]
  have mp := (volume : Measure (CalderonN.X n)).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at mp
  calc ∫ x : (CalderonN.X n), g x
      = ∫ x : ({(0:(CalderonN.X n))}ᶜ : Set (CalderonN.X n)), g x.1 ∂((volume : Measure (CalderonN.X n)).comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl g,
          restrict_compl_singleton]
    _ = ∫ p : UnitSphere n × Set.Ioi (0:ℝ),
          g ((homeomorphUnitSphereProd (CalderonN.X n)).symm p).1
          ∂((surfaceMeasure n).prod (Measure.volumeIoiPow (n-1))) := by
        have := mp.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p ↦ g ((homeomorphUnitSphereProd (CalderonN.X n)).symm p).1)
        simp only [Homeomorph.symm_apply_apply] at this
        exact this
    _ = ∫ p : UnitSphere n × Set.Ioi (0:ℝ), f p.1 * (p.2.1 ^ d * Real.exp (-p.2.1 ^ 2))
          ∂((surfaceMeasure n).prod (Measure.volumeIoiPow (n-1))) := by
        congr 1; ext ⟨ω, r⟩
        simp only [hg, homeomorphUnitSphereProd_symm_apply_coe]
        rw [hhom _ _ r.2, norm_smul, Real.norm_eq_abs, abs_of_pos r.2,
          norm_eq_of_mem_sphere ω, mul_one]
        ring
    _ = _ := by
        rw [integral_prod_mul (fun ω : UnitSphere n ↦ f ω)
          (fun r : Set.Ioi (0:ℝ) ↦ r.1 ^ d * Real.exp (-r.1 ^ 2)), radial_gamma]
        have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
        have hcast : (d : ℝ) + ((n-1 : ℕ) : ℝ) + 1 = (d : ℝ) + n := by
          rw [Nat.cast_sub hn, Nat.cast_one]
          ring
        rw [hcast]

omit [NeZero n] in
theorem eval_smul_of_isHomogeneous {p : MvPolynomial (Fin n) ℝ} {k : ℕ} (hp : p.IsHomogeneous k)
    (t : ℝ) (x : Fin n → ℝ) : eval (t • x) p = t ^ k * eval x p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = k := by
    have := hp (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

 
def pq (p q : MvPolynomial (Fin n) ℝ) (x : (CalderonN.X n)) : ℝ :=
  p.eval (x : Fin n → ℝ) * q.eval (x : Fin n → ℝ)

omit [NeZero n] in
theorem continuous_pq (p q : MvPolynomial (Fin n) ℝ) : Continuous (pq p q) := by
  unfold pq
  exact (p.continuous_eval.comp (PiLp.continuous_ofLp 2 _)).mul
    (q.continuous_eval.comp (PiLp.continuous_ofLp 2 _))

omit [NeZero n] in
theorem pq_smul {p q : MvPolynomial (Fin n) ℝ} {k m : ℕ} (hp : p.IsHomogeneous k)
    (hq : q.IsHomogeneous m) (t : ℝ) (x : (CalderonN.X n)) : pq p q (t • x) = t ^ (k + m) * pq p q x := by
  simp only [pq, WithLp.ofLp_smul, eval_smul_of_isHomogeneous hp, eval_smul_of_isHomogeneous hq]
  ring

 
theorem gaussPair_eq_sphere {p q : MvPolynomial (Fin n) ℝ} {k m : ℕ} (hp : p.IsHomogeneous k)
    (hq : q.IsHomogeneous m) :
    gaussPair p q = (∫ ω : UnitSphere n, pq p q ω ∂surfaceMeasure n) *
      (Real.Gamma ((((k + m : ℕ) : ℝ) + n) / 2) / 2) := by
  have := integral_mul_gaussian_of_homogeneous (f := pq p q) (k + m)
    (fun t x _ => pq_smul hp hq t x)
  rw [← this]
  rfl

theorem sphereInner_eq (p q : MvPolynomial (Fin n) ℝ) :
    ⟪polynomialSphereL2 p, polynomialSphereL2 q⟫_ℝ =
      (surfaceMeasure n Set.univ).toReal⁻¹ * ∫ ω : UnitSphere n, pq p q ω ∂surfaceMeasure n := by
  rw [polynomialSphereL2_inner]
  change (∫ ω : UnitSphere n, pq p q ω ∂((surfaceMeasure n univ)⁻¹ • surfaceMeasure n)) = _
  rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]


omit [NeZero n] in
theorem one_mem_harmonicHomogeneous : (1 : MvPolynomial (Fin n) ℝ) ∈ harmonicHomogeneous n 0 :=
  ⟨isHomogeneous_one _ _, by simp [laplacian]⟩

omit [NeZero n] in
theorem fischerInner_one_one : fischerInner (1 : MvPolynomial (Fin n) ℝ) 1 = 1 := by
  simp [fischerInner, fischerWeight, MvPolynomial.coeff_one]

 
theorem surface_mul_gamma (n : ℕ) [NeZero n] :
    (surfaceMeasure n Set.univ).toReal * (Real.Gamma ((n : ℝ) / 2) / 2) = Real.pi ^ ((n : ℝ) / 2) := by
  have h1 := gaussPair_eq_fischer (one_mem_harmonicHomogeneous (n := n)) one_mem_harmonicHomogeneous
  have h2 := gaussPair_eq_sphere (isHomogeneous_one (Fin n) ℝ) (isHomogeneous_one (Fin n) ℝ)
  rw [h2, fischerInner_one_one (n := n)] at h1
  have hS : ∫ ω : UnitSphere n, pq (n := n) 1 1 ω ∂surfaceMeasure n = (surfaceMeasure n Set.univ).toReal := by
    simp [pq, Measure.real]
  rw [hS] at h1
  simpa using h1

theorem gamma_half (n : ℕ) [NeZero n] (k : ℕ) :
    Real.Gamma ((((k + k : ℕ) : ℝ) + n) / 2) =
      Real.Gamma ((n : ℝ) / 2) * (sphereNormalization n k / 2 ^ k) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  induction k with
  | zero => norm_num [sphereNormalization]
  | succ k ih =>
      have harg : (((k + 1 + (k + 1) : ℕ) : ℝ) + n) / 2 = ((((k + k : ℕ) : ℝ) + n) / 2) + 1 := by
        push_cast; ring
      rw [harg, Real.Gamma_add_one (by positivity), ih]
      simp only [sphereNormalization, Finset.prod_range_succ, pow_succ]
      push_cast
      field_simp
      ring

theorem sphereFischerInner (n : ℕ) [NeZero n] : SphereFischerInner n := by
  intro k p q hp hq
  have hG := gaussPair_eq_sphere hp.1 hq.1
  rw [gaussPair_eq_fischer hp hq, gamma_half n] at hG
  have hσ := surface_mul_gamma n
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hΓ : 0 < Real.Gamma ((n : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hN : 0 < sphereNormalization n k := sphereNormalization_pos hn k
  have hπ : 0 < Real.pi ^ ((n : ℝ) / 2) := by positivity
  have hS : 0 < (surfaceMeasure n Set.univ).toReal := by
    have := hσ ▸ hπ
    nlinarith [this]
  rw [sphereInner_eq, normalizedFischerInner, Fintype.card_fin]
  set I := ∫ ω : UnitSphere n, pq p q ω ∂surfaceMeasure n
  field_simp
  rw [← hσ] at hG
  field_simp at hG
  nlinarith [hG, hΓ, hS, hN]

/-- Distinct degrees are orthogonal for the same probability sphere measure. -/
theorem orthogonalSphereHarmonics (n : ℕ) [NeZero n] : OrthogonalSphereHarmonics n := by
  intro k m hkm u hu v hv
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨q, hq, rfl⟩ := hv
  have hzero := gaussPair_eq_zero hkm hp hq
  rw [gaussPair_eq_sphere hp.1 hq.1] at hzero
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hγ : Real.Gamma ((((k+m : ℕ) : ℝ)+n)/2) / 2 ≠ 0 :=
    ne_of_gt (div_pos (Real.Gamma_pos_of_pos (by positivity)) (by norm_num))
  rw [sphereInner_eq, (mul_eq_zero.mp hzero).resolve_right hγ, mul_zero]

end OAI.AnisotropicCalderon.SphereHarmonic
