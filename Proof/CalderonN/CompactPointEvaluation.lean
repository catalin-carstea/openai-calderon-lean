module

public import Proof.CalderonN.MetricCalculus

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

public section

/- Iterated fundamental-theorem estimate from CompactPointEvaluation in
   the 3D Theorem 3.1 release, now with a Fubini induction on dimension. -/
noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff Interval ENNReal

namespace CalderonN

variable {n : ℕ}

@[expose] def wordDeriv : List (I n) → (X n → ℝ) → X n → ℝ
  | [], f => f
  | i :: w, f => coordDeriv i (wordDeriv w f)

theorem wordDeriv_append (l r : List (I n)) (f : X n → ℝ) :
    wordDeriv (l ++ r) f = wordDeriv l (wordDeriv r f) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, wordDeriv, ih]

theorem contDiff_wordDeriv (w : List (I n)) {f : X n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (wordDeriv w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    change ContDiff ℝ ∞ (coordDeriv i (wordDeriv w f))
    exact (contDiff_infty_iff_fderiv.mp ih).2.clm_apply contDiff_const

theorem tsupport_wordDeriv_subset (w : List (I n)) (f : X n → ℝ) :
    tsupport (wordDeriv w f) ⊆ tsupport f := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih => exact (tsupport_fderiv_apply_subset ℝ (axis i)).trans ih

theorem hasCompactSupport_wordDeriv (w : List (I n)) {f : X n → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (wordDeriv w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact ih.fderiv_apply (𝕜 := ℝ) (axis i)

/-- Differentiate once in each coordinate, with coordinate zero innermost. -/
@[expose] def fullCoordinateWord (n : ℕ) : List (I n) := (List.finRange n).reverse

private theorem fullCoordinateWord_succ (n : ℕ) :
    fullCoordinateWord (n+1) = (fullCoordinateWord n).map Fin.succ ++ [0] := by
  simp [fullCoordinateWord, List.finRange_succ, List.reverse_cons]

private def prepend (t : ℝ) (v : X n) : X (n+1) :=
  WithLp.toLp 2 (Fin.cons t (fun i : Fin n => v i))

private theorem prepend_zero (t : ℝ) (v : X n) : prepend t v 0 = t := rfl

private theorem prepend_succ (t : ℝ) (v : X n) (i : Fin n) :
    prepend t v i.succ = v i := by
  exact Fin.cons_succ (α := fun _ : Fin (n+1) => ℝ) t (fun j => v j) i

private theorem prepend_head_tail (v : X (n+1)) :
    prepend (v 0) (WithLp.toLp 2 fun i : Fin n => v i.succ) = v := by
  ext i
  exact Fin.cases (prepend_zero ..) (fun j => prepend_succ ..) i

private def prependTailLinear : X n →L[ℝ] X (n+1) :=
  ({ toFun := prepend 0
     map_add' u v := by
       ext i
       refine Fin.cases ?_ (fun j => ?_) i
       · simp [prepend_zero, PiLp.add_apply]
       · simp [prepend_succ, PiLp.add_apply]
     map_smul' a u := by
       ext i
       refine Fin.cases ?_ (fun j => ?_) i
       · simp [prepend_zero, PiLp.smul_apply]
       · simp [prepend_succ, PiLp.smul_apply] } : X n →ₗ[ℝ] X (n+1)).toContinuousLinearMap

private theorem prepend_eq_add (t : ℝ) (v : X n) :
    prepend t v = t • axis 0 + prependTailLinear v := by
  ext i
  change prepend t v i = ((t • axis 0 + prepend 0 v : X (n+1)) i)
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [prepend_zero, axis, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply]
  · simp [prepend_succ, axis, EuclideanSpace.single, PiLp.add_apply, PiLp.smul_apply]

private theorem prependTailLinear_axis (i : Fin n) : prependTailLinear (axis i) = axis i.succ := by
  ext j
  change prepend 0 (axis i) j = axis i.succ j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [prepend_zero, axis, EuclideanSpace.single]
  · simp [prepend_succ, axis, EuclideanSpace.single]

private theorem prepend_contDiff (t : ℝ) : ContDiff ℝ ∞ (prepend t : X n → X (n+1)) := by
  rw [show prepend t = fun v : X n => t • axis 0 + prependTailLinear v from
    funext (prepend_eq_add t)]
  exact contDiff_const.add prependTailLinear.contDiff

private theorem slice_coordDeriv {f : X (n+1) → ℝ} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (i : Fin n) :
    coordDeriv i (fun v => f (prepend t v)) = fun v => coordDeriv i.succ f (prepend t v) := by
  funext v
  have hslice : HasFDerivAt (prepend t) prependTailLinear v := by
    rw [show prepend t = fun v : X n => t • axis 0 + prependTailLinear v from
      funext (prepend_eq_add t)]
    exact prependTailLinear.hasFDerivAt.const_add (t • axis 0)
  change fderiv ℝ (f ∘ prepend t) v (axis i) = _
  rw [(((hf.differentiable (by simp) _).hasFDerivAt).comp v hslice).fderiv]
  rw [ContinuousLinearMap.comp_apply, prependTailLinear_axis]
  rfl

private theorem slice_wordDeriv (w : List (Fin n)) {f : X (n+1) → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    wordDeriv w (fun v => f (prepend t v)) =
      fun v => wordDeriv (w.map Fin.succ) f (prepend t v) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [List.map_cons, wordDeriv, ih]
      exact slice_coordDeriv (contDiff_wordDeriv _ hf) t i

private theorem support_prepend_tail {f : X (n+1) → ℝ} (hfc : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (f ∘ prepend t) := by
  obtain ⟨M, hM⟩ := hfc.isBounded.exists_norm_le
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 M)
  intro v hv
  rw [mem_closedBall_zero_iff]
  have hnorm : ‖v‖ ≤ ‖prepend t v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
    simp only [prepend_succ, le_add_iff_nonneg_left, sq_nonneg]
  exact hnorm.trans (hM _ (subset_tsupport _ hv))

private theorem support_prepend_head {f : X (n+1) → ℝ} (hfc : HasCompactSupport f) (v : X n) :
    HasCompactSupport (fun t => f (prepend t v)) := by
  obtain ⟨M, hM⟩ := hfc.isBounded.exists_norm_le
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 M)
  intro t ht
  rw [mem_closedBall_zero_iff, ← prepend_zero t v]
  exact (PiLp.norm_apply_le _ 0).trans (hM _ (subset_tsupport _ ht))

private theorem head_contDiff (v : X n) :
    ContDiff ℝ ∞ (fun t : ℝ => prepend t v) := by
  simp_rw [prepend_eq_add]
  exact (contDiff_id.smul contDiff_const).add contDiff_const

private theorem head_deriv {f : X (n+1) → ℝ} (hf : ContDiff ℝ ∞ f) (v : X n) (t : ℝ) :
    deriv (fun s => f (prepend s v)) t = coordDeriv 0 f (prepend t v) := by
  have hhead : HasDerivAt (fun s => prepend s v) (axis 0) t := by
    simp_rw [prepend_eq_add]
    simpa using ((hasDerivAt_id t).smul_const (axis 0)).add_const (prependTailLinear v)
  exact (((hf.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t hhead).deriv

private theorem abs_le_integral_abs_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (t : ℝ) : |f t| ≤ ∫ s, |deriv f s| := by
  obtain ⟨M,hM⟩ := hfc.isBounded.exists_norm_le
  let a := min (t-1) (-(|M|+1))
  have hat : a ≤ t := (min_le_left _ _).trans (by linarith)
  have ha : f a = 0 := by
    by_contra hne
    have h := hM a (subset_tsupport f hne)
    rw [Real.norm_eq_abs] at h
    have haq : a ≤ -(|M|+1) := min_le_right _ _
    linarith only [h,neg_le_abs a,le_abs_self M,haq]
  have hd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hdc : HasCompactSupport (deriv f) := by
    simpa only [fderiv_apply_one_eq_deriv] using hfc.fderiv_apply (𝕜 := ℝ) (1 : ℝ)
  have hI : IntervalIntegrable (deriv f) volume a t := hd.intervalIntegrable _ _
  have hT := intervalIntegral.integral_deriv_eq_sub
    (fun s _ => hf.differentiable (by simp) s) hI
  rw [ha,sub_zero] at hT
  rw [← hT,intervalIntegral.integral_of_le hat,← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans
    (setIntegral_le_integral (hd.norm.integrable_of_hasCompactSupport hdc.norm)
      (Filter.Eventually.of_forall fun s => norm_nonneg (deriv f s)))


private def prependEquiv : X (n+1) ≃ᵐ ℝ × X n :=
  (MeasurableEquiv.toLp 2 (Fin (n+1) → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).trans <|
      (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))

private theorem prependEquiv_symm (t : ℝ) (v : X n) :
    (prependEquiv (n := n)).symm (t,v) = prepend t v := by
  change WithLp.toLp 2 (Fin.insertNth (0 : Fin (n+1)) t (fun i : Fin n => v i)) = prepend t v
  rw [Fin.insertNth_zero']
  rfl

private theorem volume_preserving_prependEquiv : MeasurePreserving (prependEquiv (n := n)) :=
  ((MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin n))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).comp
      (PiLp.volume_preserving_ofLp (Fin (n+1))))

/-- Compact point evaluation by one fundamental-theorem estimate per coordinate. -/
theorem abs_apply_le_integral_abs_fullCoordinateWord {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : X n) :
    |f x| ≤ ∫ y, |wordDeriv (fullCoordinateWord n) f y| := by
  induction n with
  | zero =>
      rw [volume_euclideanSpace_eq_dirac]
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx, fullCoordinateWord, wordDeriv]
  | succ n ih =>
      let v : X n := WithLp.toLp 2 fun i : Fin n => x i.succ
      let g := coordDeriv 0 f
      have hg : ContDiff ℝ ∞ g := (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
      have hgc : HasCompactSupport g := hfc.fderiv_apply (𝕜 := ℝ) (axis 0)
      let h := wordDeriv ((fullCoordinateWord n).map Fin.succ) g
      have hh := contDiff_wordDeriv ((fullCoordinateWord n).map Fin.succ) hg
      have hhc := hasCompactSupport_wordDeriv ((fullCoordinateWord n).map Fin.succ) hgc
      have hft := abs_le_integral_abs_deriv (hf.comp (head_contDiff v)) (support_prepend_head hfc v) (x 0)
      change |f (prepend (x 0) v)| ≤ ∫ s, |deriv (fun t => f (prepend t v)) s| at hft
      have heq : prepend (x 0) v = x := prepend_head_tail x
      simp only [heq, head_deriv hf] at hft
      have hstep (t : ℝ) : |g (prepend t v)| ≤ ∫ y : X n, |h (prepend t y)| := by
        simpa only [Function.comp_def, slice_wordDeriv (fullCoordinateWord n) hg t, h] using
          ih (hg.comp (prepend_contDiff t)) (support_prepend_tail hgc t) v
      have hli : Integrable (fun t => |g (prepend t v)|) :=
        ((hg.comp (head_contDiff v)).continuous.abs).integrable_of_hasCompactSupport
          (support_prepend_head hgc v).abs
      have hp (q : ℝ × X n) : (prependEquiv (n := n)).symm q = prepend q.1 q.2 := by
        rcases q with ⟨t,v⟩
        exact prependEquiv_symm t v
      have hhi : Integrable (fun q : ℝ × X n => |h (prepend q.1 q.2)|) := by
        have hd : Integrable (fun y : X (n+1) => |h y|) :=
          hh.continuous.abs.integrable_of_hasCompactSupport hhc.abs
        have hs := ((volume_preserving_prependEquiv.symm _).integrable_comp_emb
          (prependEquiv (n := n)).symm.measurableEmbedding).mpr hd
        simpa only [Function.comp_def, hp] using hs
      have hFubini : (∫ t : ℝ, ∫ y : X n, |h (prepend t y)|) = ∫ y, |h y| := by
        rw [← integral_prod _ hhi]
        have he := (volume_preserving_prependEquiv.symm _).integral_comp' (fun y => |h y|)
        convert he using 1
        apply integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        rw [hp]
      rw [fullCoordinateWord_succ, wordDeriv_append]
      exact hft.trans ((integral_mono hli hhi.integral_prod_left hstep).trans_eq hFubini)

/-- Localized (L²) form of the compact point evaluation bound. -/
theorem abs_apply_le_volume_sqrt_word {f : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) {L : Set (X n)} (hL : IsCompact L) (hsub : tsupport f ⊆ L) (x : X n) :
    |f x| ≤ Real.sqrt ((volume : Measure (X n)).real L) *
      Real.sqrt (∫ y in L, wordDeriv (fullCoordinateWord n) f y ^ 2) := by
  let g := wordDeriv (fullCoordinateWord n) f
  have hfc : HasCompactSupport f := hL.of_isClosed_subset (isClosed_tsupport _) hsub
  have hgd := contDiff_wordDeriv (fullCoordinateWord n) hf
  have hgc := hasCompactSupport_wordDeriv (fullCoordinateWord n) hfc
  have h := abs_apply_le_integral_abs_fullCoordinateWord hf hfc x
  change |f x| ≤ ∫ y, |g y| at h
  have hset : (∫ y in L, |g y|) = ∫ y, |g y| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hzero : g y = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hy (hsub (tsupport_wordDeriv_subset (fullCoordinateWord n) f ht)))
    simp [hzero]
  rw [← hset] at h
  let μ := (volume : Measure (X n)).restrict L
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hL.measure_lt_top.ne
  have h₂ : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have h₁ : MemLp (fun _ : X n => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hg : MemLp g 2 μ := hgd.continuous.memLp_of_hasCompactSupport hgc
  have hg' : MemLp g (ENNReal.ofReal 2) μ := h₂.symm ▸ hg
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hg' h₁
  refine h.trans ?_
  rw [mul_comm]
  simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs, one_pow,
    integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow, μ, measureReal_def, Measure.restrict_apply_univ] using hc

end CalderonN
