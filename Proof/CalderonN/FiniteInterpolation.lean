module

public import Proof.CalderonN.PolynomialL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic

import Proof.CalderonN.Bootstrap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Adapted from `Calderon/ActualTaylorInterpolation.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc in
the earlier anisotropic Calderón formalization. The Euclidean chart type
is shared with the current statement. -/

noncomputable section
set_option autoImplicit false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory intervalIntegral Nat
open scoped Interval

/-- The degree-(40 + 2 * dim) Taylor remainder is controlled by the genuine 45th Fréchet jet
on the segment. This is the analytic remainder needed by Section 06. -/
theorem norm_sub_taylor_le (F : (X dim) → ℝ) (y h : (X dim)) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hF : ∀ t : ℝ, t ∈ Icc 0 1 → ContDiffAt ℝ (40 + 2 * dim + 1) F (y + t • h))
    (hM : ∀ t : ℝ, t ∈ Icc 0 1 → ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h)‖ ≤ M) :
    ‖F (y + h) - (∑ k ∈ Finset.range (40 + 2 * dim + 1),
      (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k F y (fun _ => h)))‖ ≤ M * ‖h‖ ^ (40 + 2 * dim + 1) := by
  have htaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := (40 + 2 * dim)) (f := F) (x := y) (y := h) hF
  rw [htaylor, add_sub_cancel_left]
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(1 - t)^(40 + 2 * dim) • iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h) (fun _ => h)‖ ≤
        M * ‖h‖^(40 + 2 * dim + 1) := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr htI.2
    have ht1 : 1 - t ≤ 1 := by linarith [htI.1]
    have hpow : |1 - t|^(40 + 2 * dim) ≤ 1 := pow_le_one₀ (abs_nonneg _) (by simpa [abs_of_nonneg ht0] using ht1)
    calc
      ‖(1 - t)^(40 + 2 * dim) • iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h) (fun _ => h)‖
          = |1 - t|^(40 + 2 * dim) * ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h) (fun _ => h)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ |1 - t|^(40 + 2 * dim) * (M * ‖h‖^(40 + 2 * dim + 1)) := by
            gcongr
            exact (ContinuousMultilinearMap.le_opNorm_mul_pow_of_le
              (iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h)) (by simp)).trans
                (mul_le_mul_of_nonneg_right (hM t htI) (pow_nonneg (norm_nonneg _) _))
      _ ≤ M * ‖h‖^(40 + 2 * dim + 1) := by nlinarith [mul_nonneg hM0 (pow_nonneg (norm_nonneg h) (40 + 2 * dim + 1))]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hint' : ‖∫ t in (0 : ℝ)..1,
      (1 - t)^(40 + 2 * dim) • iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h) (fun _ => h)‖ ≤
      M * ‖h‖^(40 + 2 * dim + 1) := by simpa using hint
  rw [norm_smul]
  have hfac : |(((40 + 2 * dim) ! : ℝ)⁻¹)| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (40 + 2 * dim))
  calc
    |(((40 + 2 * dim) ! : ℝ)⁻¹)| * ‖∫ t in (0 : ℝ)..1,
        (1 - t)^(40 + 2 * dim) • iteratedFDeriv ℝ (40 + 2 * dim + 1) F (y + t • h) (fun _ => h)‖
      ≤ 1 * (M * ‖h‖^(40 + 2 * dim + 1)) := mul_le_mul hfac hint' (norm_nonneg _) (by positivity)
    _ = M * ‖h‖^(40 + 2 * dim + 1) := one_mul _

end CalderonN



namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat

private theorem interpolation_scale_pow (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (r ^ ((1 : ℝ) / (20 + (dim : ℝ)))) ^ n = r ^ ((n : ℝ) / (20 + (dim : ℝ))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
  congr 1
  ring

private theorem interpolation_scale_remainder_power (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (r ^ ((1 : ℝ) / (20 + (dim : ℝ)))) ^ j *
        r ^ ((((40 + 2 * dim + 1 : ℕ) : ℝ) - (j : ℝ)) / (20 + (dim : ℝ))) =
      (r ^ ((1 : ℝ) / (20 + (dim : ℝ)))) ^ (40 + 2 * dim + 1) := by
  rw [interpolation_scale_pow (dim := dim) r hr j, interpolation_scale_pow (dim := dim) r hr (40 + 2 * dim + 1),
    ← Real.rpow_add hr]
  congr 1
  ring

private theorem interpolation_scale_L2_power (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (r ^ ((1 : ℝ) / (20 + (dim : ℝ)))) ^ j *
        r ^ ((2 : ℝ) - ((j : ℝ) + (dim : ℝ)/2)/(20 + (dim : ℝ))) =
      (((r ^ ((1 : ℝ) / (20 + (dim : ℝ)))) ^ dim)⁻¹) ^ ((1 : ℝ)/2) * r^2 := by
  have hhalf : (((r ^ ((dim : ℝ)/(20 + (dim : ℝ))))⁻¹) ^ ((1 : ℝ)/2)) =
      r ^ (-((dim : ℝ)/(20 + (dim : ℝ))) * (1/2 : ℝ)) := by
    rw [← Real.rpow_neg hr.le, ← Real.rpow_mul hr.le]
  rw [interpolation_scale_pow (dim := dim) r hr j, interpolation_scale_pow (dim := dim) r hr dim]
  rw [hhalf, ← Real.rpow_natCast, ← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 1
  ring

end CalderonN



namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat Filter
open scoped ContDiff Topology

private def wordJet (F : (X dim) → ℝ) (w : List (X dim)) (x : (X dim)) : ℝ :=
  iteratedFDeriv ℝ w.length F x w.get

/-- Adding a vector to a coordinate word differentiates the existing word
jet in that direction. -/
private theorem wordJet_cons_of_contDiffAt (F : (X dim) → ℝ)
    (w : List (X dim)) (v x : (X dim)) (hF : ContDiffAt ℝ ∞ F x) :
    wordJet F (v :: w) x = fderiv ℝ (wordJet F w) x v := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length F) x :=
    hF.differentiableAt_iteratedFDeriv (by
      exact_mod_cast (ENat.natCast_lt_top w.length))
  have htail : Fin.tail (v :: w).get = w.get := by
    funext i
    simp [Fin.tail, List.get]
  have h := DifferentiableAt.iteratedFDeriv_succ_apply_left'
    (f := F) (n := w.length) (x := x)
    (m := (v :: w).get) hd
  unfold wordJet
  simpa [htail] using h

/-- Every fixed word jet is twice differentiable under local smoothness. -/
private theorem contDiffAt_wordJet_two (F : (X dim) → ℝ)
    (w : List (X dim)) (x : (X dim)) (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ 2 (wordJet F w) x := by
  have hD : ContDiffAt ℝ 2 (iteratedFDeriv ℝ w.length F) x :=
    hF.iteratedFDeriv_right (by
      change (((2 : ℕ∞) + (w.length : ℕ∞) : ℕ∞) : ℕ∞ω) ≤
        ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  let ev : ((X dim) [×w.length]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.length => (X dim)) ℝ w.get
  have hev : ContDiffAt ℝ 2 ev (iteratedFDeriv ℝ w.length F x) :=
    ev.contDiff.contDiffAt
  change ContDiffAt ℝ 2
    (fun z => (iteratedFDeriv ℝ w.length F z) w.get) x
  simpa [ev, Function.comp_def] using hev.comp x hD

private theorem fderiv_fderiv_apply_const (g : (X dim) → ℝ)
    (x a b : (X dim)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fun z => fderiv ℝ g z b) x a =
      fderiv ℝ (fderiv ℝ g) x a b := by
  have hfg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := congrArg (fun T : (X dim) →L[ℝ] ℝ => T a)
    (fderiv_clm_apply hfg (differentiableAt_const b))
  simpa using h

/-- The adjacent leading vectors of a fixed word commute by finite Schwarz
symmetry; local C-infinity is available for the source fields. -/
private theorem wordJet_swap_of_contDiffOn (F : (X dim) → ℝ)
    (U : Set (X dim)) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (w : List (X dim)) (a b x : (X dim)) (hx : x ∈ U) :
    wordJet F (a :: b :: w) x = wordJet F (b :: a :: w) x := by
  let g : (X dim) → ℝ := wordJet F w
  have hFx : ContDiffAt ℝ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
  have hg : ContDiffAt ℝ 2 g x := contDiffAt_wordJet_two F w x hFx
  have hbevent : wordJet F (b :: w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ g z b) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact wordJet_cons_of_contDiffAt F w b z (hF.contDiffAt (hU.mem_nhds hz))
  have haevent : wordJet F (a :: w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ g z a) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact wordJet_cons_of_contDiffAt F w a z (hF.contDiffAt (hU.mem_nhds hz))
  have hsym := (hg.isSymmSndFDerivAt (by norm_num)).eq a b
  calc
    wordJet F (a :: b :: w) x =
      fderiv ℝ (wordJet F (b :: w)) x a :=
        wordJet_cons_of_contDiffAt F (b :: w) a x hFx
    _ = fderiv ℝ (fun z => fderiv ℝ g z b) x a := by
      rw [hbevent.fderiv_eq]
    _ = fderiv ℝ (fderiv ℝ g) x a b :=
      fderiv_fderiv_apply_const g x a b hg
    _ = fderiv ℝ (fderiv ℝ g) x b a := hsym
    _ = fderiv ℝ (fun z => fderiv ℝ g z a) x b :=
      (fderiv_fderiv_apply_const g x b a hg).symm
    _ = fderiv ℝ (wordJet F (a :: w)) x b := by
      rw [haevent.fderiv_eq]
    _ = wordJet F (b :: a :: w) x :=
      (wordJet_cons_of_contDiffAt F (a :: w) b x hFx).symm

/-- Finite Schwarz symmetry for a list of directional Fréchet evaluations on
an open smoothness domain. List permutation induction propagates the local
two-vector swap through every derivative position. -/
private theorem wordJet_perm_of_contDiffOn (F : (X dim) → ℝ)
    (U : Set (X dim)) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {w₁ w₂ : List (X dim)} (hp : w₁.Perm w₂) :
    ∀ x ∈ U, wordJet F w₁ x = wordJet F w₂ x := by
  induction hp with
  | nil =>
      intro x hx
      rfl
  | @cons a w₁ w₂ hp ih =>
      intro x hx
      have hFx : ContDiffAt ℝ ∞ F x := hF.contDiffAt (hU.mem_nhds hx)
      have hevent : wordJet F w₁ =ᶠ[𝓝 x] wordJet F w₂ := by
        filter_upwards [hU.mem_nhds hx] with z hz
        exact ih z hz
      calc
        wordJet F (a :: w₁) x =
          fderiv ℝ (wordJet F w₁) x a :=
            wordJet_cons_of_contDiffAt F w₁ a x hFx
        _ = fderiv ℝ (wordJet F w₂) x a := by
          rw [hevent.fderiv_eq]
        _ = wordJet F (a :: w₂) x :=
          (wordJet_cons_of_contDiffAt F w₂ a x hFx).symm
  | @swap a b w =>
      intro x hx
      exact wordJet_swap_of_contDiffOn F U hU hF w b a x hx
  | @trans w₁ w₂ w₃ hp₁ hp₂ ih₁ ih₂ =>
      intro x hx
      exact (ih₁ x hx).trans (ih₂ x hx)

private theorem wordJet_ofFn (F : (X dim) → ℝ) (y : (X dim))
    (k : ℕ) (v : Fin k → (X dim)) :
    wordJet F (List.ofFn v) y = iteratedFDeriv ℝ k F y v := by
  have hpair : (⟨(List.ofFn v).length, (List.ofFn v).get⟩ :
      Σ n : ℕ, Fin n → (X dim)) = ⟨k, v⟩ :=
    List.equivSigmaTuple.apply_symm_apply ⟨k, v⟩
  exact congrArg
    (fun p : Σ n : ℕ, Fin n → (X dim) =>
      iteratedFDeriv ℝ p.1 F y p.2) hpair

/-- Finite-order Schwarz symmetry of genuine iterated Fréchet derivatives on
an open smoothness domain. -/
theorem iteratedFDeriv_comp_perm_of_contDiffOn_open (F : (X dim) → ℝ)
    (U : Set (X dim)) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (y : (X dim)) (hy : y ∈ U) (k : ℕ)
    (v : Fin k → (X dim)) (σ : Equiv.Perm (Fin k)) :
    iteratedFDeriv ℝ k F y (v ∘ σ) =
      iteratedFDeriv ℝ k F y v := by
  have h := wordJet_perm_of_contDiffOn F U hU hF
    (σ.ofFn_comp_perm v) y hy
  simpa only [wordJet_ofFn] using h

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Local finite smoothness on the physical closed ball implies L² membership
of its affine pullback on the unit ball. -/
theorem memLp_affine_unitBall_of_contDiffAt_closedBall
    (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ) (hs : 0 < s)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (40 + 2 * dim + 1) F x) :
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
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply MemLp.of_bound hGmeas C
  filter_upwards [ae_restrict_mem (measurableSet_ball :
    MeasurableSet (ball (0 : (X dim)) 1))] with z hz
  exact hC z (ball_subset_closedBall hz)

end CalderonN



namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat

/-- Expansion of a genuine continuous multilinear jet in the three standard
coordinate directions. The sum is over words, before collecting monomials. -/
theorem diagonal_jet_eq_sum_coordinate_words (k : ℕ)
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

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat MvPolynomial

/-- The diagonal of every genuine Fréchet multilinear jet has a concrete
three-variable polynomial representative, with a word-indexed expansion. -/
theorem exists_diagonal_jet_mvPolynomial (k : ℕ)
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

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat MvPolynomial

/-- The actual order-(40 + 2 * dim) Fréchet Taylor sum on the scale `s` is a concrete
polynomial of total degree at most (40 + 2 * dim) in the unit-ball coordinates. -/
theorem exists_taylor_mvPolynomial (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ) :
    ∃ p : MvPolynomial (Fin dim) ℝ,
      p.totalDegree ≤ (40 + 2 * dim) ∧
      ∀ z : (X dim), MvPolynomial.eval (fun i : Fin dim => z i) p =
        ∑ k ∈ Finset.range (40 + 2 * dim + 1), (k ! : ℝ)⁻¹ •
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
    ∑ k ∈ Finset.range (40 + 2 * dim + 1), MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k) * q k
  refine ⟨p, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    have hk44 : k ≤ (40 + 2 * dim) := by
      simp only [Finset.mem_range] at hk
      omega
    calc
      (MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k) * q k).totalDegree
          ≤ (MvPolynomial.C ((k ! : ℝ)⁻¹ * s^k)).totalDegree + (q k).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ = (q k).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ k := hqdeg k
      _ ≤ (40 + 2 * dim) := hk44
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

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat MvPolynomial

/-- Any polynomial of total degree at most `m` uses exactly the finite
coordinate multi-index family of the checked L² coefficient theorem. -/
theorem exists_bounded_degree_coefficient_expansion (m : ℕ)
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

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat MvPolynomial
open scoped ENNReal

/-- The actual scaled Taylor sum has coefficients controlled by its unit-ball
L² norm, using the already checked finite-dimensional coefficient theorem. -/
theorem exists_taylor_coefficients_with_L2_bound :
    let I := {alpha : Fin dim → Fin (40 + 2 * dim + 1) // ∑ i, (alpha i).val ≤ (40 + 2 * dim)}
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ),
      ∃ a : I → ℝ,
        (∀ z : (X dim),
          (∑ k ∈ Finset.range (40 + 2 * dim + 1), (k ! : ℝ)⁻¹ •
            (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z))) =
          ∑ beta : I, a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val) ∧
        (∀ alpha : I,
          |a alpha| ≤ C *
            (eLpNorm
              (fun z : (X dim) => ∑ k ∈ Finset.range (40 + 2 * dim + 1), (k ! : ℝ)⁻¹ •
                (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)))
              2 (volume.restrict (ball (0 : (X dim)) 1))).toReal) := by
  classical
  let I := {alpha : Fin dim → Fin (40 + 2 * dim + 1) // ∑ i, (alpha i).val ≤ (40 + 2 * dim)}
  obtain ⟨C,hCpos,hC⟩ := exists_polynomial_coefficient_le_unitBall_eLpNorm (dim := dim) (40 + 2 * dim)
  refine ⟨C,hCpos,?_⟩
  intro F y s
  obtain ⟨p,hdeg,hpeval⟩ := exists_taylor_mvPolynomial F y s
  obtain ⟨a,ha⟩ := exists_bounded_degree_coefficient_expansion (40 + 2 * dim) p hdeg
  refine ⟨a,?_,?_⟩
  · intro z
    exact (hpeval z).symm.trans (ha z)
  intro alpha
  have h := hC a alpha
  simpa only [← ha, ← hpeval] using h

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat

/-- The actual Taylor remainder on the scaled unit ball, with the 45th
Fréchet norm bounded on the physical closed ball. -/
theorem norm_sub_taylor_on_unitBall_le (F : (X dim) → ℝ) (y : (X dim)) (s M : ℝ)
    (hs : 0 < s) (hM0 : 0 ≤ M)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (40 + 2 * dim + 1) F x)
    (hM : ∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F x‖ ≤ M)
    (z : (X dim)) (hz : z ∈ ball (0 : (X dim)) 1) :
    ‖F (y + s • z) - (∑ k ∈ Finset.range (40 + 2 * dim + 1),
      (k ! : ℝ)⁻¹ • (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z)))‖ ≤
        M * s^(40 + 2 * dim + 1) := by
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
  have hbase := norm_sub_taylor_le F y (s • z) M hM0
    (fun t ht => hF _ (hseg t ht)) (fun t ht => hM _ (hseg t ht))
  have hnorm : ‖s • z‖ ≤ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.le]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hz1)]
  exact hbase.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm (40 + 2 * dim + 1)) hM0)

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ContDiff

private def coordinateMonomial {m : ℕ}
    (beta : {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m})
    (z : (X dim)) : ℝ := ∏ i : Fin dim, (z i) ^ (beta.val i).val

private theorem contDiff_coordinateMonomial {m : ℕ}
    (beta : {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}) :
    ContDiff ℝ ∞ (coordinateMonomial beta) := by
  unfold coordinateMonomial
  exact contDiff_prod fun i _ => (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).contDiff.pow _

/-- Every derivative of a finite coordinate polynomial is bounded by the
corresponding coefficient-weighted sum of its genuine monomial derivatives. -/
theorem norm_iteratedFDeriv_coordinate_polynomial_le (m j : ℕ)
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
        ((contDiff_coordinateMonomial beta).of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt
      simpa only [g, smul_eq_mul, norm_smul, Real.norm_eq_abs] using congrArg norm hb

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

private def taylor (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ) (z : (X dim)) : ℝ :=
  ∑ k ∈ Finset.range (40 + 2 * dim + 1), (k ! : ℝ)⁻¹ •
    (iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z))

/-- The checked coefficient L² theorem controls each order-0-through-10
Fréchet derivative of the actual finite Taylor polynomial at the origin.
The constant is uniform in the function, center and scale. -/
theorem exists_uniform_taylor_polynomial_deriv_le_unitBall_L2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ)
      (j : ℕ), j ≤ 10 →
      ‖iteratedFDeriv ℝ j (taylor F y s) (0 : (X dim))‖ ≤
        C * (eLpNorm (taylor F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal := by
  classical
  let I := {alpha : Fin dim → Fin (40 + 2 * dim + 1) // ∑ i, (alpha i).val ≤ (40 + 2 * dim)}
  obtain ⟨Cp,hCp,hCoeff⟩ := exists_taylor_coefficients_with_L2_bound (dim := dim)
  let B : ℝ := ∑ j ∈ Finset.range 11,
    ∑ beta : I, ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨Cp * (B + 1), mul_pos hCp (by linarith), ?_⟩
  intro F y s j hj
  obtain ⟨a,ha,hca⟩ := hCoeff F y s
  have hfun : taylor F y s =
      fun z : (X dim) => ∑ beta : I, a beta * coordinateMonomial beta z := by
    funext z
    simpa only [taylor, coordinateMonomial] using ha z
  have hB : (∑ beta : I,
      ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖) ≤ B := by
    change (∑ beta : I, ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖) ≤
      ∑ k ∈ Finset.range 11, ∑ beta : I, ‖iteratedFDeriv ℝ k (coordinateMonomial beta) (0 : (X dim))‖
    exact Finset.single_le_sum
      (s := Finset.range 11)
      (f := fun k => ∑ beta : I,
        ‖iteratedFDeriv ℝ k (coordinateMonomial beta) (0 : (X dim))‖)
      (a := j)
      (fun k hk => Finset.sum_nonneg (fun beta _ => norm_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hN0 : 0 ≤ (eLpNorm (taylor F y s) 2
      (volume.restrict (ball (0 : (X dim)) 1))).toReal := ENNReal.toReal_nonneg
  calc
    ‖iteratedFDeriv ℝ j (taylor F y s) (0 : (X dim))‖
      = ‖iteratedFDeriv ℝ j
          (fun z : (X dim) => ∑ beta : I, a beta * coordinateMonomial beta z)
          (0 : (X dim))‖ := by rw [hfun]
    _
      ≤ ∑ beta : I, |a beta| *
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖ :=
            norm_iteratedFDeriv_coordinate_polynomial_le (40 + 2 * dim) j a
    _ ≤ ∑ beta : I,
        (Cp * (eLpNorm (taylor F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal) *
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖ := by
            apply Finset.sum_le_sum
            intro beta _
            exact mul_le_mul_of_nonneg_right (hca beta) (norm_nonneg _)
    _ = (Cp * (eLpNorm (taylor F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal) *
        (∑ beta : I,
          ‖iteratedFDeriv ℝ j (coordinateMonomial beta) (0 : (X dim))‖) := by
            rw [Finset.mul_sum]
    _ ≤ (Cp * (eLpNorm (taylor F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal) * B := by
            exact mul_le_mul_of_nonneg_left hB (mul_nonneg hCp.le hN0)
    _ ≤ (Cp * (B + 1)) *
        (eLpNorm (taylor F y s) 2
          (volume.restrict (ball (0 : (X dim)) 1))).toReal := by
            nlinarith [mul_nonneg hCp.le hN0]

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

/-- The derivative of the actual finite Taylor sum recovers the scaled source
jet. The explicit symmetry premise isolates the finite-order Schwarz step. -/
theorem iteratedFDeriv_taylor_at_zero_of_symmetric (F : (X dim) → ℝ)
    (y : (X dim)) (s : ℝ) (j : ℕ) (hj : j ≤ (40 + 2 * dim))
    (hSym : ∀ k : ℕ, k ≤ (40 + 2 * dim) → ∀ (v : Fin k → (X dim)) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℝ k F y (v ∘ σ) = iteratedFDeriv ℝ k F y v) :
    iteratedFDeriv ℝ j (taylor F y s) (0 : (X dim)) =
      s^j • iteratedFDeriv ℝ j F y := by
  classical
  let p : FormalMultilinearSeries ℝ (X dim) ℝ := fun k =>
    if k < (40 + 2 * dim + 1) then ((k ! : ℝ)⁻¹ * s^k) • iteratedFDeriv ℝ k F y else 0
  have hfinite (k : ℕ) (hk : (40 + 2 * dim + 1) ≤ k) : p k = 0 := by simp only [p, if_neg (show ¬k < 40 + 2 * dim + 1 by omega)]
  have hsum (z : (X dim)) :
      (∑ k ∈ Finset.range (40 + 2 * dim + 1), p k (fun _ : Fin k => z)) = taylor F y s z := by
    simp only [p, Finset.sum_apply, Finset.mem_range, dite_true, taylor]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < (40 + 2 * dim + 1) := Finset.mem_range.mp hk
    rw [if_pos hk']
    have hscale := (iteratedFDeriv ℝ k F y).toMultilinearMap.map_smul_univ
      (fun _ : Fin k => s) (fun _ : Fin k => z)
    change iteratedFDeriv ℝ k F y (fun _ : Fin k => s • z) =
      (∏ _i : Fin k, s) * iteratedFDeriv ℝ k F y (fun _ : Fin k => z) at hscale
    rw [hscale]
    simp only [Finset.prod_const, Finset.card_fin, smul_apply, smul_eq_mul]
    ring
  have hseries : HasFiniteFPowerSeriesOnBall (taylor F y s) p
      (0 : (X dim)) (40 + 2 * dim + 1) ∞ := by
    apply HasFiniteFPowerSeriesOnBall.mk' hfinite (by simp)
    intro z hz
    simpa only [zero_add] using (hsum z)
  have hjlt : j < (40 + 2 * dim + 1) := by omega
  have hderiv (v : Fin j → (X dim)) :=
    hseries.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace v
  ext v
  rw [hderiv]
  have hpj : p j = ((j ! : ℝ)⁻¹ * s^j) • iteratedFDeriv ℝ j F y := by
    simp only [p, if_pos hjlt]
  simp only [hpj, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hsym (σ : Equiv.Perm (Fin j)) :
      iteratedFDeriv ℝ j F y (fun i => v (σ i)) = iteratedFDeriv ℝ j F y v :=
    hSym j hj v σ
  simp_rw [hsym]
  simp [Fintype.card_perm, mul_assoc, Nat.factorial_ne_zero]

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Exact three-dimensional Jacobian for the affine chart of the physical
interpolation ball. -/
theorem map_volume_restrict_unitBall_affine (y : (X dim)) (s : ℝ) (hs : 0 < s) :
    Measure.map (fun z : (X dim) => y + s • z)
      (volume.restrict (ball (0 : (X dim)) 1)) =
    ENNReal.ofReal ((s^dim)⁻¹) •
      (volume.restrict (ball y s)) := by
  have hsmul : Measure.map (fun z : (X dim) => s • z) volume =
      ENNReal.ofReal ((s^dim)⁻¹) • (volume : Measure (X dim)) := by
    convert Measure.map_addHaar_smul (volume : Measure (X dim)) hs.ne' using 1
    simp [finrank_euclideanSpace_fin, abs_of_pos (pow_pos hs dim)]
  have hmap : Measure.map (fun z : (X dim) => y + s • z) volume =
      ENNReal.ofReal ((s^dim)⁻¹) • (volume : Measure (X dim)) := by
    calc
      Measure.map (fun z : (X dim) => y + s • z) volume =
          Measure.map (fun x : (X dim) => x + y)
            (Measure.map (fun z : (X dim) => s • z) volume) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              congr 1
              funext z
              simp [Function.comp_def, add_comm]
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

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Exact L² change of variables from the physical radius-`s` ball to the
unit ball; the factor is the square root of the inverse 3D Jacobian. -/
theorem eLpNorm_affine_unitBall_eq_scaled_physicalBall
    (F : (X dim) → ℝ) (hF : Measurable F) (y : (X dim)) (s : ℝ) (hs : 0 < s) :
    eLpNorm (fun z : (X dim) => F (y + s • z)) 2
        (volume.restrict (ball (0 : (X dim)) 1)) =
      (ENNReal.ofReal ((s^dim)⁻¹)) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm F 2 (volume.restrict (ball y s)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((s^dim)⁻¹)
  have hc : c ≠ 0 := by
    have hs3 : 0 < s^dim := pow_pos hs _
    simp [c, hs3]
  have hmap := map_volume_restrict_unitBall_affine y s hs
  have htransport := eLpNorm_map_measure
    (p := (2 : ℝ≥0∞)) (f := fun z : (X dim) => y + s • z)
    (g := F) (μ := volume.restrict (ball (0 : (X dim)) 1))
    (hF.aestronglyMeasurable)
    (by fun_prop : AEMeasurable (fun z : (X dim) => y + s • z)
      (volume.restrict (ball (0 : (X dim)) 1)))
  rw [hmap] at htransport
  have hscalar := eLpNorm_smul_measure_of_ne_zero hc F
    (2 : ℝ≥0∞) (volume.restrict (ball y s))
  simpa only [c, smul_eq_mul, Function.comp_def] using htransport.symm.trans hscalar

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- Real-valued form of the exact physical-ball L² scaling factor. -/
theorem eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall
    (F : (X dim) → ℝ) (hF : Measurable F) (y : (X dim)) (s : ℝ) (hs : 0 < s) :
    (eLpNorm (fun z : (X dim) => F (y + s • z)) 2
        (volume.restrict (ball (0 : (X dim)) 1))).toReal =
      ((s^dim)⁻¹) ^ ((1 : ℝ) / 2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by
  rw [eLpNorm_affine_unitBall_eq_scaled_physicalBall F hF y s hs,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  have hs3 : 0 ≤ s^dim := (pow_pos hs dim).le
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hs3)]
  norm_num

end CalderonN


namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- A bounded pointwise Taylor remainder gives an actual L² bound for its
polynomial on the unit ball. -/
theorem lpNorm_taylor_le_affine_lpNorm_add_remainder
    (F : (X dim) → ℝ) (y : (X dim)) (s M : ℝ)
    (hs : 0 < s) (hM0 : 0 ≤ M)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (40 + 2 * dim + 1) F x)
    (hM : ∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F x‖ ≤ M)
    (hLp : MemLp (fun z : (X dim) => F (y + s • z)) 2
      (volume.restrict (ball (0 : (X dim)) 1))) :
    (eLpNorm (taylor F y s) 2
      (volume.restrict (ball (0 : (X dim)) 1))).toReal ≤
      (eLpNorm (fun z : (X dim) => F (y + s • z)) 2
        (volume.restrict (ball (0 : (X dim)) 1))).toReal +
      M * s^(40 + 2 * dim + 1) *
        ((volume.restrict (ball (0 : (X dim)) 1)).real .univ ^
          (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)) := by
  let μ : Measure (X dim) := volume.restrict (ball (0 : (X dim)) 1)
  let G : (X dim) → ℝ := fun z => F (y + s • z)
  let P : (X dim) → ℝ := taylor F y s
  have hPcont : Continuous P := by
    obtain ⟨p, _, hp⟩ := exists_taylor_mvPolynomial F y s
    have hPeq : P = fun z : (X dim) => MvPolynomial.eval (fun i : Fin dim => z i) p := by
      funext z
      exact (hp z).symm
    rw [hPeq]
    exact (MvPolynomial.continuous_eval p).comp (by fun_prop)
  have hPmeas : AEStronglyMeasurable P μ := hPcont.measurable.aestronglyMeasurable
  have hRmeas : AEStronglyMeasurable (G - P) μ :=
    hLp.aestronglyMeasurable.sub hPmeas
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hRbound : ∀ᵐ z ∂μ, ‖(G - P) z‖ ≤ M * s^(40 + 2 * dim + 1) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : (X dim)) 1))]
      with z hz
    exact norm_sub_taylor_on_unitBall_le F y s M hs hM0 hF hM z hz
  have hRlp : MemLp (G - P) 2 μ :=
    MemLp.of_bound hRmeas (M * s^(40 + 2 * dim + 1)) hRbound
  have hRnorm : lpNorm (G - P) 2 μ ≤
      M * s^(40 + 2 * dim + 1) * (μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)) := by
    have hClp : MemLp (fun _ : (X dim) => M * s^(40 + 2 * dim + 1)) 2 μ := memLp_const _
    calc
      lpNorm (G - P) 2 μ ≤ lpNorm (fun _ : (X dim) => M * s^(40 + 2 * dim + 1)) 2 μ := by
        exact ENNReal.toReal_mono hClp.eLpNorm_ne_top
          (eLpNorm_mono_ae_real hRmeas hRbound)
      _ = _ := by
        rw [lpNorm_const' (by norm_num) (by norm_num)]
        simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM0 (pow_nonneg hs.le _))]
  have hPsub : P = G - (G - P) := by
    funext z
    simp [G, P]
  change lpNorm P 2 μ ≤ lpNorm G 2 μ +
    M * s^(40 + 2 * dim + 1) * (μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ))
  rw [hPsub]
  calc
    lpNorm (G - (G - P)) 2 μ ≤ lpNorm G 2 μ + lpNorm (G - P) 2 μ :=
      lpNorm_sub_le hLp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ _ := add_le_add_right hRnorm _

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- The affine L² change of variables only needs measurability on the
physical ball. -/
theorem eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall_local
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

/-- Local smoothness supplies the measurability needed in the preceding
physical-ball change of variables. -/
theorem aestronglyMeasurable_physicalBall_of_contDiffAt_closedBall
    (F : (X dim) → ℝ) (y : (X dim)) (s : ℝ)
    (hF : ∀ x ∈ closedBall y s, ContDiffAt ℝ (40 + 2 * dim + 1) F x) :
    AEStronglyMeasurable F (volume.restrict (ball y s)) := by
  have hcont : ContinuousOn F (closedBall y s) :=
    continuousOn_of_forall_continuousAt fun x hx => (hF x hx).continuousAt
  exact hcont.aestronglyMeasurable_of_subset_isCompact
    (isCompact_closedBall y s) measurableSet_ball ball_subset_closedBall

end CalderonN

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal

/-- The complete finite-order Taylor/L² estimate up to the finite Schwarz
symmetry identity. Its constant is uniform in the function, center and scale,
and the L² norm is on the actual physical ball. -/
theorem exists_uniform_taylor_jet_le_physicalBall_L2_of_symmetric :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (y : (X dim)) (s M : ℝ)
      (j : ℕ), 0 < s → 0 ≤ M →
      (∀ x ∈ closedBall y s, ContDiffAt ℝ (40 + 2 * dim + 1) F x) →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F x‖ ≤ M) →
      (∀ k : ℕ, k ≤ (40 + 2 * dim) → ∀ (v : Fin k → (X dim)) (σ : Equiv.Perm (Fin k)),
        iteratedFDeriv ℝ k F y (v ∘ σ) = iteratedFDeriv ℝ k F y v) →
      j ≤ 10 →
      s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
        C * (((s^dim)⁻¹)^((1 : ℝ)/2) *
          (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^(40 + 2 * dim + 1)) := by
  obtain ⟨Cp,hCp,hPoly⟩ := exists_uniform_taylor_polynomial_deriv_le_unitBall_L2 (dim := dim)
  let μ : Measure (X dim) := volume.restrict (ball (0 : (X dim)) 1)
  let V : ℝ := μ.real .univ ^ (((2 : ℝ≥0∞).toReal)⁻¹ : ℝ)
  have hV0 : 0 ≤ V := by
    dsimp [V]
    positivity
  refine ⟨Cp * (V+1), mul_pos hCp (by linarith), ?_⟩
  intro F y s M j hs hM0 hF hM hSym hj
  have hFscaledLp := memLp_affine_unitBall_of_contDiffAt_closedBall F y s hs hF
  have hL2 := lpNorm_taylor_le_affine_lpNorm_add_remainder
    F y s M hs hM0 hF hM hFscaledLp
  have hFmeas := aestronglyMeasurable_physicalBall_of_contDiffAt_closedBall F y s hF
  have hscale := eLpNorm_affine_unitBall_toReal_eq_scaled_physicalBall_local
    F y s hs hFmeas
  have hpoly := hPoly F y s j hj
  have hjet := iteratedFDeriv_taylor_at_zero_of_symmetric F y s j
    (by omega : j ≤ (40 + 2 * dim)) hSym
  have hpow : 0 ≤ s^j := (pow_pos hs _).le
  have hN0 : 0 ≤ (eLpNorm F 2 (volume.restrict (ball y s))).toReal :=
    ENNReal.toReal_nonneg
  have hX0 : 0 ≤ ((s^dim)⁻¹)^((1 : ℝ)/2) *
      (eLpNorm F 2 (volume.restrict (ball y s))).toReal := by positivity
  have hY0 : 0 ≤ M*s^(40 + 2 * dim + 1) := mul_nonneg hM0 (pow_nonneg hs.le _)
  have hjetnorm : ‖iteratedFDeriv ℝ j (taylor F y s) (0 : (X dim))‖ =
      s^j * ‖iteratedFDeriv ℝ j F y‖ := by
    rw [hjet, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpow]
  have hN : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      Cp * (((s^dim)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal +
        M*s^(40 + 2 * dim + 1)*V) := by
    calc
      _ = ‖iteratedFDeriv ℝ j (taylor F y s) (0 : (X dim))‖ := hjetnorm.symm
      _ ≤ Cp * (eLpNorm (taylor F y s) 2 μ).toReal := hpoly
      _ ≤ Cp * ((eLpNorm (fun z : (X dim) => F (y+s•z)) 2 μ).toReal +
          M*s^(40 + 2 * dim + 1)*V) := mul_le_mul_of_nonneg_left hL2 hCp.le
      _ = _ := by rw [hscale]
  calc
    s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      Cp * (((s^dim)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal +
        M*s^(40 + 2 * dim + 1)*V) := hN
    _ ≤ Cp * (V+1) *
      (((s^dim)⁻¹)^((1 : ℝ)/2) *
        (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^(40 + 2 * dim + 1)) := by
      nlinarith [mul_nonneg hCp.le hX0, mul_nonneg hCp.le hY0,
        mul_nonneg hV0 hX0, mul_nonneg hV0 hY0]

end CalderonN


namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

/-- Actual local smoothness discharges finite Schwarz symmetry in the
physical-ball Taylor/L² interpolation estimate. -/
public theorem exists_uniform_taylor_jet_le_physicalBall_L2_of_contDiffOn :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (U : Set (X dim))
      (y : (X dim)) (s M : ℝ) (j : ℕ),
      IsOpen U → ContDiffOn ℝ ∞ F U → y ∈ U →
      closedBall y s ⊆ U → 0 < s → 0 ≤ M →
      (∀ x ∈ closedBall y s, ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F x‖ ≤ M) →
      j ≤ 10 →
      s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
        C * (((s^dim)⁻¹)^((1 : ℝ)/2) *
          (eLpNorm F 2 (volume.restrict (ball y s))).toReal + M*s^(40 + 2 * dim + 1)) := by
  obtain ⟨C,hC,hInterp⟩ :=
    exists_uniform_taylor_jet_le_physicalBall_L2_of_symmetric (dim := dim)
  refine ⟨C,hC,?_⟩
  intro F U y s M j hU hF hy hBall hs hM0 hM hj
  have h45 : ((40 + 2 * dim + 1) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    change (((40 + 2 * dim + 1) : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hF45 : ∀ x ∈ closedBall y s, ContDiffAt ℝ (40 + 2 * dim + 1) F x := by
    intro x hx
    exact (hF.contDiffAt (hU.mem_nhds (hBall hx))).of_le h45
  exact hInterp F y s M j hs hM0 hF45 hM
    (fun k _hk v σ =>
      iteratedFDeriv_comp_perm_of_contDiffOn_open F U hU hF y hy k v σ)
    hj

end CalderonN


namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory Nat
open scoped ENNReal ContDiff

/-- The Section 06 choice s=r^(1/(20 + (dim : ℝ))), m=(40 + 2 * dim + 1) and j≤10 yields the genuine
three-halves derivative gain from a physical-ball L² bound of order r². -/
public theorem exists_uniform_taylor_jet_le_three_halves_of_local_L2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (X dim) → ℝ) (U : Set (X dim))
      (y : (X dim)) (r A M : ℝ) (j : ℕ),
      IsOpen U → ContDiffOn ℝ ∞ F U → y ∈ U →
      0 < r → r ≤ 1 → 0 ≤ A → 0 ≤ M →
      closedBall y (r ^ ((1 : ℝ)/(20 + (dim : ℝ)))) ⊆ U →
      (∀ x ∈ closedBall y (r ^ ((1 : ℝ)/(20 + (dim : ℝ)))),
        ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) F x‖ ≤ M) →
      (eLpNorm F 2
        (volume.restrict (ball y (r ^ ((1 : ℝ)/(20 + (dim : ℝ))))))).toReal ≤ A*r^2 →
      j ≤ 10 →
      ‖iteratedFDeriv ℝ j F y‖ ≤ C*(A+M)*r^(3/2 : ℝ) := by
  obtain ⟨C,hC,hInterp⟩ :=
    exists_uniform_taylor_jet_le_physicalBall_L2_of_contDiffOn (dim := dim)
  refine ⟨C,hC,?_⟩
  intro F U y r A M j hU hF hy hr hr1 hA0 hM0 hBall hM hL2 hj
  let s : ℝ := r ^ ((1 : ℝ)/(20 + (dim : ℝ)))
  let qA : ℝ := r ^ ((2 : ℝ) - ((j : ℝ) + (dim : ℝ)/2)/(20 + (dim : ℝ)))
  let qB : ℝ := r ^ ((((40 + 2 * dim + 1 : ℕ) : ℝ) - (j : ℝ))/(20 + (dim : ℝ)))
  let scale : ℝ := ((s^dim)⁻¹)^((1 : ℝ)/2)
  have hs : 0 < s := Real.rpow_pos_of_pos hr _
  have hsj : 0 < s^j := pow_pos hs _
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hBridge := hInterp F U y s M j hU hF hy hBall hs hM0 hM hj
  have hL2' : (eLpNorm F 2 (volume.restrict (ball y s))).toReal ≤ A*r^2 := hL2
  have hN : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      C*(scale*(A*r^2)+M*s^(40 + 2 * dim + 1)) := by
    exact hBridge.trans <|
      mul_le_mul_of_nonneg_left
        (add_le_add_left (mul_le_mul_of_nonneg_left hL2' hscale0) _) hC.le
  have hPowA : s^j * qA = scale*r^2 := by
    simpa [s, qA, scale] using interpolation_scale_L2_power (dim := dim) r hr j
  have hPowB : s^j * qB = s^(40 + 2 * dim + 1) := by
    simpa [s, qB] using interpolation_scale_remainder_power (dim := dim) r hr j
  have hBound : s^j * ‖iteratedFDeriv ℝ j F y‖ ≤
      s^j*(C*(A*qA+M*qB)) := by
    calc
      _ ≤ C*(scale*(A*r^2)+M*s^(40 + 2 * dim + 1)) := hN
      _ = C*(A*(scale*r^2)+M*s^(40 + 2 * dim + 1)) := by ring
      _ = C*(A*(s^j*qA)+M*(s^j*qB)) := by rw [hPowA, hPowB]
      _ = s^j*(C*(A*qA+M*qB)) := by ring
  have hCancel : ‖iteratedFDeriv ℝ j F y‖ ≤ C*(A*qA+M*qB) :=
    le_of_mul_le_mul_left hBound hsj
  have hExp :=
    interpolation_powers_le_three_halves hr hr1 hj (n := dim) (m := 40 + 2 * dim + 1) (by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) dim])
  have hDen : (2 : ℝ) * (10 + (dim : ℝ) / 2) = 20 + (dim : ℝ) := by ring
  rw [hDen] at hExp
  have hExpA : qA ≤ r^(3/2 : ℝ) := hExp.1
  have hExpB : qB ≤ r^(3/2 : ℝ) := hExp.2
  calc
    ‖iteratedFDeriv ℝ j F y‖ ≤ C*(A*qA+M*qB) := hCancel
    _ ≤ C*((A+M)*r^(3/2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      calc
        A*qA+M*qB ≤ A*r^(3/2 : ℝ)+M*r^(3/2 : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hExpA hA0)
            (mul_le_mul_of_nonneg_left hExpB hM0)
        _ = (A+M)*r^(3/2 : ℝ) := by ring
    _ = C*(A+M)*r^(3/2 : ℝ) := by ring

end CalderonN
