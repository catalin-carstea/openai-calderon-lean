module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Proof.CalderonN.PolynomialL2
import Proof.CalderonN.TaylorJetSymmetry
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-! The finite-order interpolation argument generalizes the fixed-order proof in
the released Proof.CalderonN.FiniteInterpolation, commit
4d97dc89403377fef662b4643360b2ec01be1460. -/

noncomputable section
open CalderonN MeasureTheory Metric Set Nat Filter MvPolynomial intervalIntegral Module
open scoped ContDiff ENNReal Interval

namespace CalderonPaper

set_option maxHeartbeats 1000000
variable {dim : ℕ} [NeZero dim]

private def taylor (degree : ℕ) (F : X dim → ℝ) (y : X dim) (s : ℝ) (z : X dim) : ℝ :=
  ∑ k ∈ Finset.range (degree + 1), (k ! : ℝ)⁻¹ •
    iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)

private def coordinateMonomial {degree : ℕ}
    (a : {alpha : Fin dim → Fin (degree + 1) // ∑ i, (alpha i).val ≤ degree})
    (z : X dim) : ℝ := ∏ i : Fin dim, (z i) ^ (a.val i).val


omit [NeZero dim] in
private theorem diagonal_jet_eq_sum_coordinate_words (k : ℕ)
    (T : (X dim) [×k]→L[ℝ] ℝ) (z : (X dim)) :
    T (fun _ : Fin k => z) =
      ∑ w : Fin k → Fin dim,
        (∏ j : Fin k, z (w j)) *
          T (fun j : Fin k => EuclideanSpace.basisFun (Fin dim) ℝ (w j)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin dim) ℝ
  have hz : z = ∑ i : Fin dim, z i • b i := by
    simpa [b] using (b.sum_repr z).symm
  calc
    T (fun _ : Fin k => z) =
        T (fun _ : Fin k => ∑ i : Fin dim, z i • b i) := by rw [← hz]
    _ = ∑ w : Fin k → Fin dim,
          T (fun j : Fin k => z (w j) • b (w j)) := by
            exact T.toMultilinearMap.map_sum (fun (_j : Fin k) (i : Fin dim) => z i • b i)
    _ = ∑ w : Fin k → Fin dim,
          (∏ j : Fin k, z (w j)) * T (fun j : Fin k => b (w j)) := by
            apply Finset.sum_congr rfl
            intro w _
            exact (T.toMultilinearMap.map_smul_univ (fun j : Fin k => z (w j))
                (fun j : Fin k => b (w j)))
    _ = _ := rfl

omit [NeZero dim] in
private theorem exists_diagonal_jet_mvPolynomial (k : ℕ)
    (T : (X dim) [×k]→L[ℝ] ℝ) :
    ∃ p : MvPolynomial (Fin dim) ℝ,
      p.totalDegree ≤ k ∧
      ∀ z : (X dim), MvPolynomial.eval (fun i : Fin dim => z i) p =
        T (fun _ : Fin k => z) := by
  classical
  let p : MvPolynomial (Fin dim) ℝ :=
    ∑ w : Fin k → Fin dim,
      MvPolynomial.C (T (fun j : Fin k => EuclideanSpace.basisFun (Fin dim) ℝ (w j))) *
        ∏ j : Fin k, MvPolynomial.X (w j)
  refine ⟨p, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro w _
    calc
      (MvPolynomial.C (T (fun j : Fin k => EuclideanSpace.basisFun (Fin dim) ℝ (w j))) *
          ∏ j : Fin k, MvPolynomial.X (w j)).totalDegree
          ≤ (MvPolynomial.C (T (fun j : Fin k => EuclideanSpace.basisFun (Fin dim) ℝ (w j)))).totalDegree +
              (∏ j : Fin k, MvPolynomial.X (w j)).totalDegree :=
                MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + ∑ j : Fin k, (MvPolynomial.X (w j) : MvPolynomial (Fin dim) ℝ).totalDegree := by
            simp only [MvPolynomial.totalDegree_C, zero_add]
            exact MvPolynomial.totalDegree_finsetProd (Finset.univ : Finset (Fin k))
              (fun j => (MvPolynomial.X (w j) : MvPolynomial (Fin dim) ℝ))
      _ = k := by simp
  intro z
  have hw := diagonal_jet_eq_sum_coordinate_words k T z
  rw [hw]
  simp only [p, map_sum, map_mul, map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro w _
  ring

omit [NeZero dim] in
private theorem exists_bounded_degree_coefficient_expansion (m : ℕ)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p.totalDegree ≤ m) :
    let I := {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
    ∃ a : I → ℝ, ∀ z : (X dim),
      MvPolynomial.eval (fun i : Fin dim => z i) p =
        ∑ beta : I, a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val := by
  classical
  let I := {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
  let e : I → (Fin dim →₀ ℕ) := fun beta =>
    Finsupp.equivFunOnFinite.symm (fun i => (beta.val i).val)
  have he : Function.Injective e := by
    intro alpha beta h
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hi := congrArg (fun d : Fin dim →₀ ℕ => d i) h
    simpa only [e, Finsupp.coe_equivFunOnFinite_symm] using hi
  have hsurj (d : Fin dim →₀ ℕ) (hd : d ∈ p.support) : ∃ beta : I, e beta = d := by
    have hdi (i : Fin dim) : d i ≤ m :=
      ((MvPolynomial.le_degreeOf_of_mem_support i hd).trans
        (MvPolynomial.degreeOf_le_totalDegree p i)).trans hp
    let beta : I := ⟨fun i => ⟨d i, Nat.lt_succ_of_le (hdi i)⟩, by
      simpa only [Finsupp.sum_fintype (f := d) (g := fun _ e => e) (by simp)] using
        (MvPolynomial.le_totalDegree hd).trans hp⟩
    refine ⟨beta, ?_⟩
    ext i
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rfl
  let a : I → ℝ := fun beta => p.coeff (e beta)
  let q : MvPolynomial (Fin dim) ℝ := ∑ beta : I, MvPolynomial.monomial (e beta) (a beta)
  have hpq : p = q := by
    ext d
    by_cases hd : d ∈ p.support
    · obtain ⟨beta, hbeta⟩ := hsurj d hd
      subst d
      simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      have hsum : (∑ gamma : I, if e gamma = e beta then a gamma else 0) = a beta := by
        simp only [he.eq_iff]
        exact Fintype.sum_ite_eq' beta a
      simpa only [a] using hsum.symm
    · have hzero : p.coeff d = 0 := by simpa only [MvPolynomial.mem_support_iff, not_ne_iff] using hd
      simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      rw [hzero]
      symm
      apply Finset.sum_eq_zero
      intro beta _
      by_cases h : e beta = d
      · simp only [h, ↓reduceIte, a, hzero]
      · simp [h]

  refine ⟨a, ?_⟩
  intro z
  rw [hpq]
  simp only [q, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro beta _
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

omit [NeZero dim] in
private theorem contDiff_coordinateMonomial {m : ℕ}
    (beta : {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}) :
    ContDiff ℝ ∞ (coordinateMonomial beta) := by
  unfold coordinateMonomial
  exact contDiff_prod fun i _ => (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).contDiff.pow _

omit [NeZero dim] in
private theorem norm_iteratedFDeriv_coordinate_polynomial_le (m j : ℕ)
    (a : {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m} → ℝ) :
    ‖iteratedFDeriv ℝ j
      (fun z : (X dim) => ∑ beta, a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val)
      (0 : (X dim))‖ ≤
    ∑ beta, |a beta| * ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖ := by
  classical
  let I := {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
  let g : I → (X dim) → ℝ := fun beta z => a beta * coordinateMonomial beta z
  have hg (beta : I) : ContDiffAt ℝ j (g beta) (0 : (X dim)) := by
    exact ((contDiff_const.mul (contDiff_coordinateMonomial beta)).of_le (by simp)).contDiffAt
  have hsum := iteratedFDeriv_fun_sum_apply (u := Finset.univ) (x := (0 : (X dim)))
    (fun beta _ => hg beta)
  change iteratedFDeriv ℝ j (fun z : (X dim) => ∑ beta : I, g beta z) (0 : (X dim)) =
    ∑ beta : I, iteratedFDeriv ℝ j (g beta) (0 : (X dim)) at hsum
  change ‖iteratedFDeriv ℝ j (fun z : (X dim) => ∑ beta : I, g beta z) (0 : (X dim))‖ ≤
    ∑ beta : I, |a beta| * ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖
  rw [hsum]
  calc
    ‖∑ beta : I, iteratedFDeriv ℝ j (g beta) (0 : (X dim))‖
        ≤ ∑ beta : I, ‖iteratedFDeriv ℝ j (g beta) (0 : (X dim))‖ := norm_sum_le _ _
    _ = ∑ beta : I, |a beta| * ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖ := by
      apply Finset.sum_congr rfl
      intro beta _
      have hb := iteratedFDeriv_const_smul_apply'
        (i := j) (x := (0 : (X dim))) (a := a beta) (f := coordinateMonomial beta)
        ((contDiff_coordinateMonomial beta).of_le (by simp : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt
      simpa only [g, smul_eq_mul, norm_smul, Real.norm_eq_abs] using congrArg norm hb

omit [NeZero dim] in
private theorem map_volume_restrict_unitBall_affine (y : (X dim)) (s : ℝ) (hs : 0 < s) :
    Measure.map (fun z : (X dim) => y + s • z)
      (volume.restrict (ball (0 : (X dim)) 1)) =
    ENNReal.ofReal ((s^dim)⁻¹) •
      (volume.restrict (ball y s)) := by
  have hsmul : Measure.map (fun z : (X dim) => s • z) volume =
      ENNReal.ofReal ((s^dim)⁻¹) • (volume : Measure (X dim)) := by
    convert Measure.map_addHaar_smul (volume : Measure (X dim)) hs.ne' using 1
    simp [abs_of_pos (pow_pos hs dim)]
  have hmap : Measure.map (fun z : (X dim) => y + s • z) volume =
      ENNReal.ofReal ((s^dim)⁻¹) • (volume : Measure (X dim)) := by
    calc
      Measure.map (fun z : (X dim) => y + s • z) volume =
          Measure.map (fun x : (X dim) => x + y)
            (Measure.map (fun z : (X dim) => s • z) volume) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              congr 1
              funext z
              simp [add_comm]
      _ = ENNReal.ofReal ((s^dim)⁻¹) • (volume : Measure (X dim)) := by
            rw [hsmul, Measure.map_smul _ (by fun_prop)]
            simp only [map_add_right_eq_self]
  have hpre : (fun z : (X dim) => y + s • z) ⁻¹' ball y s = ball (0 : (X dim)) 1 := by
    ext z
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs, sub_zero]
    constructor
    · intro h
      by_contra hn
      have hn' : 1 ≤ ‖z‖ := le_of_not_gt hn
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hn')]
    · intro h
      nlinarith [mul_pos hs (sub_pos.mpr h)]
  have hmeasure := Measure.restrict_map
    (μ := (volume : Measure (X dim))) (f := fun z : (X dim) => y + s • z)
    (by fun_prop : Measurable fun z : (X dim) => y + s • z)
    (s := ball y s) isOpen_ball.measurableSet
  rw [hmap, hpre] at hmeasure
  simpa only [Measure.restrict_smul] using hmeasure.symm

omit [NeZero dim] in
private theorem eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall_local
    (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ) (hs : 0 < s)
    (hF : AEStronglyMeasurable F (volume.restrict (ball y s))) :
    (eLpNorm (fun z : (X dim) => F (y + s • z)) 2
        (volume.restrict (ball (0 : (X dim)) 1))).toReal =
      ((s^dim)⁻¹) ^ ((1 : ℝ) / 2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((s^dim)⁻¹)
  have hc : c ≠ 0 := by
    have hs3 : 0 < s^dim := pow_pos hs _
    simp [c, hs3]
  have hmap := map_volume_restrict_unitBall_affine y s hs
  have hFmap : AEStronglyMeasurable F
      (Measure.map (fun z : (X dim) => y + s • z)
        (volume.restrict (ball (0 : (X dim)) 1))) := by
    rw [hmap]
    exact hF.smul_measure c
  have htransport := eLpNorm_map_measure
    (p := (2 : ℝ≥0∞)) (f := fun z : (X dim) => y + s • z)
    (g := F) (μ := volume.restrict (ball (0 : (X dim)) 1))
    hFmap
    (by fun_prop : AEMeasurable (fun z : (X dim) => y + s • z)
      (volume.restrict (ball (0 : (X dim)) 1)))
  rw [hmap] at htransport
  have hscalar := eLpNorm_smul_measure_of_ne_zero hc F
    (2 : ℝ≥0∞) (volume.restrict (ball y s))
  have hnorm : eLpNorm (fun z : (X dim) => F (y + s • z)) 2
      (volume.restrict (ball (0 : (X dim)) 1)) =
        c ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          eLpNorm F 2 (volume.restrict (ball y s)) := by
    simpa only [smul_eq_mul, Function.comp_def] using htransport.symm.trans hscalar
  rw [hnorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  have hs3 : 0 ≤ s^dim := (pow_pos hs dim).le
  simp only [c, ENNReal.toReal_ofReal (inv_nonneg.mpr hs3)]
  norm_num

omit [NeZero dim] in
private theorem norm_sub_taylor_le (degree : ℕ) (F : (X dim) → ℝ) (y h : (X dim)) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hF : ∀ t : ℝ, t ∈ Icc 0 1 → ContDiffAt ℝ (degree + 1 : ℕ) F (y + t • h))
    (hM : ∀ t : ℝ, t ∈ Icc 0 1 → ‖iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h)‖ ≤ M) :
    ‖F (y + h) - (∑ k ∈ Finset.range (degree + 1),
      (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k F y (fun _ => h)))‖ ≤ M * ‖h‖ ^ (degree + 1) := by
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := degree) (f := F) (x := y) (y := h) hF
  rw [htaylor, add_sub_cancel_left]
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(1 - t)^(degree) • iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h) (fun _ => h)‖ ≤
        M * ‖h‖^(degree + 1) := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr htI.2
    have ht1 : 1 - t ≤ 1 := by linarith [htI.1]
    have hpow : |1 - t|^(degree) ≤ 1 := pow_le_one₀ (abs_nonneg _) (by simpa [abs_of_nonneg ht0] using ht1)
    calc
      ‖(1 - t)^(degree) • iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h) (fun _ => h)‖
          = |1 - t|^(degree) * ‖iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h) (fun _ => h)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ |1 - t|^(degree) * (M * ‖h‖^(degree + 1)) := by
            gcongr
            exact (ContinuousMultilinearMap.le_opNorm_mul_pow_of_le
              (iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h)) (by simp)).trans
                (mul_le_mul_of_nonneg_right (hM t htI) (pow_nonneg (norm_nonneg _) _))
      _ ≤ M * ‖h‖^(degree + 1) := by nlinarith [mul_nonneg hM0 (pow_nonneg (norm_nonneg h) (degree + 1))]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hint' : ‖∫ t in (0 : ℝ)..1,
      (1 - t)^(degree) • iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h) (fun _ => h)‖ ≤
      M * ‖h‖^(degree + 1) := by simpa using hint
  rw [norm_smul]
  have hfac : |(((degree) ! : ℝ)⁻¹)| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (degree))
  calc
    |(((degree) ! : ℝ)⁻¹)| * ‖∫ t in (0 : ℝ)..1,
        (1 - t)^(degree) • iteratedFDeriv ℝ (degree + 1 : ℕ) F (y + t • h) (fun _ => h)‖
      ≤ 1 * (M * ‖h‖^(degree + 1)) := mul_le_mul hfac hint' (norm_nonneg _) (by positivity)
    _ = M * ‖h‖^(degree + 1) := one_mul _

omit [NeZero dim] in
private theorem memLp_affine_unitBall (degree : ℕ)
    (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ) (hs : 0 < s)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (degree + 1 : ℕ) F x) :
    MemLp (fun z : (X dim) => F (y + s • z)) 2
      (volume.restrict (ball (0 : (X dim)) 1)) := by
  let G : (X dim) → ℝ := fun z => F (y + s • z)
  let K : Set (X dim) := closedBall (0 : (X dim)) 1
  let μ : Measure (X dim) := volume.restrict (ball (0 : (X dim)) 1)
  have hmap (z : (X dim)) (hz : z ∈ K) : y + s • z ∈ closedBall y s := by
    have hz' : ‖z‖ ≤ 1 := by
      simpa [K, mem_closedBall, dist_eq_norm] using hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hz')]
  have hGcont : ContinuousOn G K := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    have hAff : ContinuousAt (fun w : (X dim) => y + s • w) z := by fun_prop
    exact ContinuousAt.comp' (hF _ (hmap z hz)).continuousAt hAff
  have hKcompact : IsCompact K := isCompact_closedBall (0 : (X dim)) 1
  have hGmeas : AEStronglyMeasurable G μ :=
    hGcont.aestronglyMeasurable_of_subset_isCompact hKcompact measurableSet_ball
      (by exact ball_subset_closedBall)
  obtain ⟨C,hC⟩ := hKcompact.exists_bound_of_continuousOn hGcont
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply MemLp.of_bound hGmeas C
  filter_upwards [ae_restrict_mem (measurableSet_ball :
    MeasurableSet (ball (0 : (X dim)) 1))] with z hz
  exact hC z (ball_subset_closedBall hz)

omit [NeZero dim] in
private theorem exists_taylor_mvPolynomial (degree : ℕ) (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ) :
    ∃ p : MvPolynomial (Fin dim) ℝ,
      p.totalDegree ≤ (degree) ∧
      ∀ z : (X dim), MvPolynomial.eval (fun i : Fin dim => z i) p =
        ∑ k ∈ Finset.range (degree + 1), (k ! : ℝ)⁻¹ •
          (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)) := by
  classical
  let T (k : ℕ) : (X dim) [×k]→L[ℝ] ℝ := iteratedFDeriv ℝ k F y
  have hq (k : ℕ) : ∃ p : MvPolynomial (Fin dim) ℝ,
      p.totalDegree ≤ k ∧
      ∀ z : (X dim), MvPolynomial.eval (fun i : Fin dim => z i) p =
        T k (fun _ : Fin k => z) := exists_diagonal_jet_mvPolynomial k (T k)
  let q (k : ℕ) : MvPolynomial (Fin dim) ℝ := Classical.choose (hq k)
  have hqdeg (k : ℕ) : (q k).totalDegree ≤ k := (Classical.choose_spec (hq k)).1
  have hqeval (k : ℕ) (z : (X dim)) :
      MvPolynomial.eval (fun i : Fin dim => z i) (q k) = T k (fun _ : Fin k => z) :=
        (Classical.choose_spec (hq k)).2 z
  let p : MvPolynomial (Fin dim) ℝ :=
    ∑ k ∈ Finset.range (degree + 1), MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k) * q k
  refine ⟨p, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    have hk44 : k ≤ (degree) := by
      simp only [Finset.mem_range] at hk
      omega
    calc
      (MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k) * q k).totalDegree
          ≤ (MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k)).totalDegree + (q k).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = (q k).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ k := hqdeg k
      _ ≤ (degree) := hk44
  intro z
  have hs (k : ℕ) :
      T k (fun _ : Fin k => s • z) = s^k * T k (fun _ : Fin k => z) := by
    have h := (T k).toMultilinearMap.map_smul_univ (fun _ : Fin k => s)
      (fun _ : Fin k => z)
    change T k (fun _ : Fin k => s • z) = (∏ _j : Fin k, s) * T k (fun _ : Fin k => z) at h
    simpa only [Finset.prod_const, Finset.card_fin, nsmul_eq_mul] using h
  simp only [p, map_sum, map_mul, MvPolynomial.eval_C, hqeval]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hs]
  simp only [smul_eq_mul]
  ring

private theorem exists_taylor_coefficients_with_L2_bound (degree : ℕ) :
    let I := {alpha : Fin dim → Fin (degree + 1) // ∑ i, (alpha i).val ≤ (degree)}
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ),
      ∃ a : I → ℝ,
        (∀ z : (X dim),
          (∑ k ∈ Finset.range (degree + 1), (k ! : ℝ)⁻¹ •
            (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z))) =
          ∑ beta : I, a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val) ∧
        (∀ alpha : I,
          |a alpha| ≤ C *
            (eLpNorm
              (fun z : (X dim) => ∑ k ∈ Finset.range (degree + 1), (k ! : ℝ)⁻¹ •
                (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)))
              2 (volume.restrict (ball (0 : (X dim)) 1))).toReal) := by
  classical
  let I := {alpha : Fin dim → Fin (degree + 1) // ∑ i, (alpha i).val ≤ (degree)}
  obtain ⟨C,hCpos,hC⟩ := exists_polynomial_coefficient_le_unitBall_eLpNorm (dim := dim) (degree)
  refine ⟨C,hCpos,?_⟩
  intro F y s
  obtain ⟨p,hdeg,hpeval⟩ := exists_taylor_mvPolynomial degree F y s
  obtain ⟨a,ha⟩ := exists_bounded_degree_coefficient_expansion (degree) p hdeg
  refine ⟨a,?_,?_⟩
  · intro z
    exact (hpeval z).symm.trans (ha z)
  intro alpha
  have h := hC a alpha
  simpa only [← ha, ← hpeval] using h

omit [NeZero dim] in
private theorem norm_sub_taylor_on_unitBall_le (degree : ℕ) (F : (X dim) → ℝ) (y : (X dim)) (s M : ℝ)
    (hs : 0 < s) (hM0 : 0 ≤ M)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (degree + 1 : ℕ) F x)
    (hM : ∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (degree + 1 : ℕ) F x‖ ≤ M)
    (z : (X dim)) (hz : z ∈ ball (0 : (X dim)) 1) :
    ‖F (y + s • z) - (∑ k ∈ Finset.range (degree + 1),
      (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)))‖ ≤
        M * s^(degree + 1) := by
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  have hseg (t : ℝ) (ht : t ∈ Icc 0 1) : y + t • (s • z) ∈ closedBall y s := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have ht0 : 0 ≤ t := ht.1
    have hts : 0 ≤ t * s := mul_nonneg ht0 hs.le
    have htsle : t * s ≤ s := by nlinarith [ht.2]
    rw [abs_of_nonneg ht0, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le]
    calc
      t * (s * ‖z‖) = (t * s) * ‖z‖ := by ring
      _ ≤ (t * s) * 1 := mul_le_mul_of_nonneg_left hz1 hts
      _ ≤ s := by simpa using htsle
  have hbase := norm_sub_taylor_le degree F y (s • z) M hM0
    (fun t ht => hF _ (hseg t ht)) (fun t ht => hM _ (hseg t ht))
  have hnorm : ‖s • z‖ ≤ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hz1)]
  exact hbase.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm (degree + 1)) hM0)

private theorem exists_uniform_taylor_polynomial_deriv_le_unitBall_L2 (degree : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ)
      (j : ℕ), j ≤ degree →
      ‖iteratedFDeriv ℝ j (taylor degree F y s) (0 : (X dim))‖ ≤
        C * (eLpNorm (taylor degree F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal := by
  classical
  let I := {alpha : Fin dim → Fin (degree + 1) // ∑ i, (alpha i).val ≤ (degree)}
  obtain ⟨Cp,hCp,hCoeff⟩ := exists_taylor_coefficients_with_L2_bound degree (dim := dim)
  let B : ℝ := ∑ j ∈ Finset.range (degree + 1),
    ∑ beta : I, ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Cp * (B + 1), mul_pos hCp (by linarith), ?_⟩
  intro F y s j hj
  obtain ⟨a,ha,hca⟩ := hCoeff F y s
  have hfun : taylor degree F y s =
      fun z : (X dim) => ∑ beta : I, a beta * coordinateMonomial beta z := by
    funext z
    simpa only [taylor, coordinateMonomial] using ha z
  have hB : (∑ beta : I,
      ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖) ≤ B := by
    change (∑ beta : I, ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖) ≤
      ∑ k ∈ Finset.range (degree + 1), ∑ beta : I, ‖iteratedFDeriv ℝ k (coordinateMonomial beta) (0 : (X dim))‖
    exact Finset.single_le_sum
      (s := Finset.range (degree + 1))
      (f := fun k => ∑ beta : I,
        ‖iteratedFDeriv ℝ k (coordinateMonomial beta) (0 : (X dim))‖)
      (a := j)
      (fun k hk => Finset.sum_nonneg (fun beta _ => norm_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hN0 : 0 ≤ (eLpNorm (taylor degree F y s) 2
      (volume.restrict (ball (0 : (X dim)) 1))).toReal := ENNReal.toReal_nonneg
  calc
    ‖iteratedFDeriv ℝ j (taylor degree F y s) (0 : (X dim))‖
      = ‖iteratedFDeriv ℝ j
          (fun z : (X dim) => ∑ beta : I, a beta * coordinateMonomial beta z)
          (0 : (X dim))‖ := by rw [hfun]
    _
      ≤ ∑ beta : I, |a beta| *
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖ :=
            norm_iteratedFDeriv_coordinate_polynomial_le (degree) j a
    _ ≤ ∑ beta : I,
        (Cp * (eLpNorm (taylor degree F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal) *
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖ := by
            apply Finset.sum_le_sum
            intro beta _
            exact mul_le_mul_of_nonneg_right (hca beta) (norm_nonneg _)
    _ = (Cp * (eLpNorm (taylor degree F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal) *
        (∑ beta : I,
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖) := by
            rw [Finset.mul_sum]
    _ ≤ (Cp * (eLpNorm (taylor degree F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal) * B := by
            exact mul_le_mul_of_nonneg_left hB (mul_nonneg hCp.le hN0)
    _ ≤ (Cp * (B + 1)) *
        (eLpNorm (taylor degree F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal := by
            nlinarith [mul_nonneg hCp.le hN0]

omit [NeZero dim] in
private theorem iteratedFDeriv_taylor_at_zero (degree : ℕ) (F : (X dim) → ℝ)
    (y : (X dim)) (s : ℝ) (j : ℕ) (hj : j ≤ (degree))
    (hSym : ∀ k : ℕ, k ≤ (degree) → ∀ (v : Fin k → (X dim)) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℝ k F y (v ∘ σ) = iteratedFDeriv ℝ k F y v) :
    iteratedFDeriv ℝ j (taylor degree F y s) (0 : (X dim)) =
      s^j • iteratedFDeriv ℝ j F y := by
  classical
  let p : FormalMultilinearSeries ℝ (X dim) ℝ := fun k =>
    if k < (degree + 1) then ((k ! : ℝ)⁻¹ * s^k) • iteratedFDeriv ℝ k F y else 0
  have hfinite (k : ℕ) (hk : (degree + 1) ≤ k) : p k = 0 := by simp only [p, ite_eq_right (show ¬k < degree + 1 by omega)]
  have hsum (z : (X dim)) :
      (∑ k ∈ Finset.range (degree + 1), p k (fun _ : Fin k => z)) = taylor degree F y s z := by
    simp only [p, taylor]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < (degree + 1) := Finset.mem_range.mp hk
    rw [ite_eq_left hk']
    have hscale := (iteratedFDeriv ℝ k F y).toMultilinearMap.map_smul_univ
      (fun _ : Fin k => s) (fun _ : Fin k => z)
    change iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z) =
      (∏ _i : Fin k, s) * iteratedFDeriv ℝ k F y (fun _ : Fin k => z) at hscale
    rw [hscale]
    simp only [Finset.prod_const, Finset.card_fin, smul_apply, smul_eq_mul]
    ring
  have hseries : HasFiniteFPowerSeriesOnBall (taylor degree F y s) p
      (0 : (X dim)) (degree + 1) ∞ := by
    apply HasFiniteFPowerSeriesOnBall.mk' hfinite (by simp)
    intro z hz
    simpa only [zero_add] using (hsum z)
  have hjlt : j < (degree + 1) := by omega
  have hderiv (v : Fin j → (X dim)) :=
    hseries.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace v
  ext v
  rw [hderiv]
  have hpj : p j = ((j ! : ℝ)⁻¹ * s^j) • iteratedFDeriv ℝ j F y := by
    simp only [p, ite_eq_left hjlt]
  simp only [hpj, smul_apply, smul_eq_mul]
  have hsym (σ : Equiv.Perm (Fin j)) :
      iteratedFDeriv ℝ j F y (fun i => v (σ i)) = iteratedFDeriv ℝ j F y v :=
    hSym j hj v σ
  simp_rw [hsym]
  simp [Fintype.card_perm, mul_assoc, Nat.factorial_ne_zero]

private theorem lpNorm_taylor_le_affine_lpNorm_add_remainder (degree : ℕ)
    (F : (X dim) → ℝ) (y : (X dim)) (s M : ℝ)
    (hs : 0 < s) (hM0 : 0 ≤ M)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (degree + 1 : ℕ) F x)
    (hM : ∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (degree + 1 : ℕ) F x‖ ≤ M)
    (hLp : MemLp (fun z : (X dim) => F (y + s • z)) 2
      (volume.restrict (ball (0 : (X dim)) 1))) :
    (eLpNorm (taylor degree F y s) 2
      (volume.restrict (ball (0 : (X dim)) 1))).toReal ≤
      (eLpNorm (fun z : (X dim) => F (y + s • z)) 2
        (volume.restrict (ball (0 : (X dim)) 1))).toReal +
      M * s^(degree + 1) *
        ((volume.restrict (ball (0 : (X dim)) 1)).real .univ ^
          (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)) := by
  let μ : Measure (X dim) := volume.restrict (ball (0 : (X dim)) 1)
  let G : (X dim) → ℝ := fun z => F (y + s • z)
  let P : (X dim) → ℝ := taylor degree F y s
  have hPcont : Continuous P := by
    obtain ⟨p, _, hp⟩ := exists_taylor_mvPolynomial degree F y s
    have hPeq : P = fun z : (X dim) => MvPolynomial.eval (fun i : Fin dim => z i) p := by
      funext z
      exact (hp z).symm
    rw [hPeq]
    exact (MvPolynomial.continuous_eval p).comp (by fun_prop)
  have hPmeas : AEStronglyMeasurable P μ := hPcont.measurable.aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (G - P) μ :=
    hLp.aestronglyMeasurable.sub hPmeas
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hRbound : ∀ᵐ z ∂μ, ‖(G - P) z‖ ≤ M * s^(degree + 1) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : (X dim)) 1))]
      with z hz
    exact norm_sub_taylor_on_unitBall_le degree F y s M hs hM0 hF hM z hz
  have hRlp : MemLp (G - P) 2 μ :=
    MemLp.of_bound hRmeas (M * s^(degree + 1)) hRbound
  have hRnorm : lpNorm (G - P) 2 μ ≤
      M * s^(degree + 1) * (μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)) := by
    have hClp : MemLp (fun _ : (X dim) => M * s^(degree + 1)) 2 μ := memLp_const _
    calc
      lpNorm (G - P) 2 μ ≤ lpNorm (fun _ : (X dim) => M * s^(degree + 1)) 2 μ := by
        exact ENNReal.toReal_mono hClp.eLpNorm_ne_top
          (eLpNorm_mono_ae_real hRmeas hRbound)
      _ = _ := by
        rw [lpNorm_const' (by norm_num) (by norm_num)]
        simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM0 (pow_nonneg hs.le _))]
  have hPsub : P = G - (G - P) := by
    funext z
    simp [G, P]
  change lpNorm P 2 μ ≤ lpNorm G 2 μ +
    M * s^(degree + 1) * (μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ))
  rw [hPsub]
  calc
    lpNorm (G - (G - P)) 2 μ ≤ lpNorm G 2 μ + lpNorm (G - P) 2 μ :=
      lpNorm_sub_le hLp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ _ := add_le_add_right hRnorm _

omit [NeZero dim] in
private theorem aestronglyMeasurable_physicalBall (degree : ℕ)
    (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (degree + 1 : ℕ) F x) :
    AEStronglyMeasurable F (volume.restrict (ball y s)) := by
  have hcont : ContinuousOn F (closedBall y s) :=
    continuousOn_of_forall_continuousAt fun x hx => (hF x hx).continuousAt
  exact hcont.aestronglyMeasurable_of_subset_isCompact
    (isCompact_closedBall y s) measurableSet_ball ball_subset_closedBall

private theorem exists_uniform_taylor_jet_le_physicalBall_L2 (degree : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (y : (X dim)) (s M : ℝ)
      (j : ℕ), 0 < s → 0 ≤ M →
      (∀ x ∈ closedBall y s, ContDiffAt ℝ (degree + 1 : ℕ) F x) →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (degree + 1 : ℕ) F x‖ ≤ M) →
      (∀ k : ℕ, k ≤ (degree) → ∀ (v : Fin k → (X dim)) (σ : Equiv.Perm (Fin k)),
        iteratedFDeriv ℝ k F y (v ∘ σ) = iteratedFDeriv ℝ k F y v) →
      j ≤ degree →
      s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
        C * (((s^dim)⁻¹)^((1 : ℝ)/2) *
          (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^(degree + 1)) := by
  obtain ⟨Cp,hCp,hPoly⟩ := exists_uniform_taylor_polynomial_deriv_le_unitBall_L2 degree (dim := dim)
  let μ : Measure (X dim) := volume.restrict (ball (0 : (X dim)) 1)
  let V : ℝ := μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)
  have hV0 : 0 ≤ V := by
    dsimp [V]
    positivity
  refine ⟨Cp * (V+1), mul_pos hCp (by linarith), ?_⟩
  intro F y s M j hs hM0 hF hM hSym hj
  have hFscaledLp := memLp_affine_unitBall degree F y s hs hF
  have hL2 := lpNorm_taylor_le_affine_lpNorm_add_remainder degree
    F y s M hs hM0 hF hM hFscaledLp
  have hFmeas := aestronglyMeasurable_physicalBall degree F y s hF
  have hscale := eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall_local
    F y s hs hFmeas
  have hpoly := hPoly F y s j hj
  have hjet := iteratedFDeriv_taylor_at_zero degree F y s j
    (by omega : j ≤ (degree)) hSym
  have hpow : 0 ≤ s^j := (pow_pos hs _).le
  have hN0 : 0 ≤ (eLpNorm F 2 (volume.restrict (ball y s))).toReal :=
    ENNReal.toReal_nonneg
  have hX0 : 0 ≤ ((s^dim)⁻¹)^((1 : ℝ)/2) *
      (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by positivity
  have hY0 : 0 ≤ M*s^(degree + 1) := mul_nonneg hM0 (pow_nonneg hs.le _)
  have hjetnorm : ‖iteratedFDeriv ℝ j (taylor degree F y s) (0 : (X dim))‖ =
      s^j * ‖iteratedFDeriv ℝ j F y‖ := by
    rw [hjet, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpow]
  have hN : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      Cp * (((s^dim)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal +
        M*s^(degree + 1)*V) := by
    calc
      _ = ‖iteratedFDeriv ℝ j (taylor degree F y s) (0 : (X dim))‖ := hjetnorm.symm
      _ ≤ Cp * (eLpNorm (taylor degree F y s) 2 μ).toReal := hpoly
      _ ≤ Cp * ((eLpNorm (fun z : (X dim) => F (y+s•z)) 2 μ).toReal +
          M*s^(degree + 1)*V) := mul_le_mul_of_nonneg_left hL2 hCp.le
      _ = _ := by rw [hscale]
  calc
    s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      Cp * (((s^dim)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal +
        M*s^(degree + 1)*V) := hN
    _ ≤ Cp * (V+1) *
      (((s^dim)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^(degree + 1)) := by
      nlinarith [mul_nonneg hCp.le hX0, mul_nonneg hCp.le hY0,
        mul_nonneg hV0 hX0, mul_nonneg hV0 hY0]

end CalderonPaper

public section

namespace CalderonPaper

/-- Lemma 6.2 of the pinned manuscript. The jet estimate is written in the
equivalent operator norm and multiplied by the positive factor `s^j`.
The bound on the order-`m` jet is supplied by the manuscript's `C^m` bound. -/
theorem lemma62 (dim m : ℕ) [NeZero dim] :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : X dim → ℝ) (U : Set (X dim)) (y : X dim)
        (s A : ℝ) (j : ℕ),
      IsOpen U → ContDiffOn ℝ ∞ F U → closedBall y s ⊆ U →
      0 < s → s ≤ 1 → 0 ≤ A →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ m F x‖ ≤ A) →
      j < m →
      s ^ j * ‖iteratedFDeriv ℝ j F y‖ ≤ C *
        (((s ^ dim)⁻¹) ^ ((1 : ℝ) / 2) *
          lpNorm F 2 (volume.restrict (ball y s)) + A * s ^ m) := by
  cases m with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro F U y s A j _ _ _ _ _ _ _ hj
    omega
  | succ degree =>
    obtain ⟨C, hC, h⟩ := exists_uniform_taylor_jet_le_physicalBall_L2 (dim := dim) degree
    refine ⟨C, hC, ?_⟩
    intro F U y s A j hU hF hBall hs _ hA hM hj
    have hy : y ∈ U := hBall (mem_closedBall_self hs.le)
    have hF' (x) (hx : x ∈ closedBall y s) : ContDiffAt ℝ (degree + 1 : ℕ) F x := by
      exact (hF.contDiffAt (hU.mem_nhds (hBall hx))).of_le (by simp)
    exact h F y s A j hs hA hF' hM
      (fun k _ v σ => by
        have hInt : U ⊆ closure (interior U) := by
          rw [hU.interior_eq]
          exact subset_closure
        simpa only [iteratedFDerivWithin_of_isOpen k hU hy] using
          iteratedFDerivWithin_perm hU.uniqueDiffOn hInt hF k y hy v σ)
      (Nat.le_of_lt_succ hj)

end CalderonPaper
