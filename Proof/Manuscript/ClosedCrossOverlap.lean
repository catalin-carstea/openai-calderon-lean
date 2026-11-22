module

public import Proof.Manuscript.ScalarCrossSlices
public import Proof.CalderonN.CrossSeriesAgreement
public import Proof.CalderonN.CrossRangeClosure

import Proof.CalderonN.CrossWeakContinuation
import Mathlib.MeasureTheory.Measure.SeparableMeasure

public section

open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ENNReal

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {dim : ℕ}

-- Adapted from the released Proof.CalderonN.CrossOverlap. The Hilbert
-- expansion only uses the closed range and measurable slice data.

/-- The original Hilbert expansion gives first-arm agreement, including
the case in which only a portion of the observed second arm overlaps. -/
theorem closedCrossSeries_ae_eq_firstArm
    {D₁ S₂ O₁ O₂ B : Set (X dim)} (H : ClosedSubmodule ℝ (ChartL2 D₁))
    (hO₁ : O₁ ⊆ D₁) (hBS : B ⊆ S₂) (hBO : B ⊆ O₂)
    (hfinite : (volume : Measure (X dim)) S₂ ≠ ⊤)
    {ι : Type*} [Countable ι] (w : HilbertBasis ι ℝ (H))
    (b : ι → ChartL2 O₂) (q : ChartProductL2 (d := dim) D₁ S₂)
    (hslice : ∀ᵐ y ∂(volume : Measure (X dim)).restrict S₂, ∃ u : H,
      (u.1 : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict D₁] fun x => q (x,y))
    (hb : ∀ i, (b i : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict B] tensorCoefficient (w i).1 q)
    {Q : ChartProductL2 O₁ O₂}
    (habs : Summable fun i => ‖tensorLp (closedRestrict H hO₁ (w i)) (b i)‖)
    (hQ : HasSum (fun i => tensorLp (closedRestrict H hO₁ (w i)) (b i)) Q) :
    (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict O₁).prod ((volume : Measure (X dim)).restrict B)] q := by
  let hm := Measure.restrict_mono_set (volume : Measure (X dim)) hO₁
  let hn := Measure.restrict_mono_set (volume : Measure (X dim)) hBS
  let hn' := Measure.restrict_mono_set (volume : Measure (X dim)) hBO
  let : IsFiniteMeasure (chartMeasure S₂) := isFiniteMeasure_restrict.mpr hfinite
  let q' := restrictL2 (Measure.prod_mono hm hn) q
  have hq' := restrictL2_ae (Measure.prod_mono hm hn) q
  have hqswap := (Measure.measurePreserving_swap (μ := chartMeasure B)
    (ν := chartMeasure O₁)).quasiMeasurePreserving.ae hq'
  have hcoef (i : ι) : ∀ᵐ y ∂chartMeasure B,
      b i y = ∫ x, (w i).1 x * q (x,y) ∂chartMeasure D₁ := by
    exact Filter.EventuallyEq.trans (hb i) (ae_mono hn (tensorCoefficient_ae_integral (w i).1 q))
  refine Filter.EventuallyEq.trans (tensorSeries_ae_eq_of_slice_hasSum le_rfl hn'
    _ b habs hQ q' ?_) hq'
  filter_upwards [ae_mono hn hslice, ae_all_iff.mpr hcoef, Measure.ae_ae_of_ae_prod hqswap]
    with y hy hyb hys
  obtain ⟨u, hu⟩ := hy
  let R := closedRestrict H hO₁
  refine ⟨R u, ?_, ?_⟩
  · have hentry : (fun x => q' (x,y)) =ᵐ[chartMeasure O₁] fun x => q (x,y) := hys
    exact (closedRestrict_ae H hO₁ u).trans
      (Filter.EventuallyEq.trans (ae_mono hm hu) hentry.symm)
  · have hyre (i : ι) : b i y = inner ℝ (w i) u := by
      rw [hyb i]
      change _ = inner ℝ (w i).1 u.1
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
    have hre (i : ι) : restrictL2 le_rfl (R (w i)) = R (w i) :=
      Lp.ext (restrictL2_ae le_rfl (R (w i)))
    change HasSum (fun i => b i y • restrictL2 le_rfl (R (w i))) (R u)
    simpa only [hyre, hre, map_smul, w.repr_apply_apply] using R.hasSum (w.hasSum_repr u)

set_option maxHeartbeats 900000 in
/-- The restricted singular basis reconstructs the second arm wherever
its actual slices belong to the closed restriction range. -/
theorem closedCrossSeries_ae_eq_secondArm
    {D₁ D₂ S₁ O₁ O₂ A : Set (X dim)} (H : ClosedSubmodule ℝ (ChartL2 D₁))
    (hAS : A ⊆ S₁) (hAO : A ⊆ O₁) (hO₁ : O₁ ⊆ D₁) (hS₁ : S₁ ⊆ D₁) (hO₂ : O₂ ⊆ D₂)
    (hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (w : HilbertBasis ι ℝ (H)) (μ : ι → ℝ) (hμ : ∀ i, 0 < μ i)
    (hgram : ∀ i j, inner ℝ (closedRestrict H hS₁ (w i))
      (closedRestrict H hS₁ (w j)) = if i = j then μ i ^ 2 else 0)
    (b : ι → ChartL2 O₂) (q : ChartProductL2 (d := dim) S₁ D₂)
    (hslice : ∀ᵐ y ∂(volume : Measure (X dim)).restrict D₂,
      ∃ u ∈ closure (range (closedRestrict H hS₁)),
        (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict S₁] fun x => q (x,y))
    (hb : ∀ i, (b i : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict O₂]
      crossArmCoefficient (closedRestrict H hS₁ (w i)) (μ i) q)
    {Q : ChartProductL2 O₁ O₂}
    (habs : Summable fun i => ‖tensorLp (closedRestrict H hO₁ (w i)) (b i)‖)
    (hQ : HasSum (fun i => tensorLp (closedRestrict H hO₁ (w i)) (b i)) Q) :
    (Q : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict A).prod ((volume : Measure (X dim)).restrict O₂)] q := by
  let hm := Measure.restrict_mono_set (volume : Measure (X dim)) hAS
  let hm' := Measure.restrict_mono_set (volume : Measure (X dim)) hAO
  let hn := Measure.restrict_mono_set (volume : Measure (X dim)) hO₂
  let : IsFiniteMeasure (chartMeasure D₂) := isFiniteMeasure_restrict.mpr hfinite
  let q' := restrictL2 (Measure.prod_mono hm hn) q
  let R := closedRestrict H hS₁
  let J := closedRestrict H hO₁
  have hq' := restrictL2_ae (Measure.prod_mono hm hn) q
  have hqswap := (Measure.measurePreserving_swap (μ := chartMeasure O₂)
    (ν := chartMeasure A)).quasiMeasurePreserving.ae hq'
  have hcoef (i : ι) : ∀ᵐ y ∂chartMeasure O₂,
      b i y = (μ i ^ 2)⁻¹ * ∫ x, R (w i) x * q (x,y) ∂chartMeasure S₁ :=
    Filter.EventuallyEq.trans (hb i) (ae_mono hn (crossArmCoefficient_ae_integral (R (w i)) (μ i) q))
  refine Filter.EventuallyEq.trans (tensorSeries_ae_eq_of_slice_hasSum hm' le_rfl
    (fun i => J (w i)) b habs hQ q' ?_) hq'
  filter_upwards [ae_mono hn hslice, ae_all_iff.mpr hcoef, Measure.ae_ae_of_ae_prod hqswap]
    with y hy hyb hys
  obtain ⟨u, huR, hu⟩ := hy
  refine ⟨restrictL2 hm u, ?_, ?_⟩
  · have hentry : (fun x => q' (x,y)) =ᵐ[chartMeasure A] fun x => q (x,y) := hys
    exact (restrictL2_ae hm u).trans
      (Filter.EventuallyEq.trans (ae_mono hm hu) hentry.symm)
  · have hyre (i : ι) : b i y = singularCoefficient R w μ i u := by
      rw [hyb i, singularCoefficient_apply, L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [RCLike.inner_apply, conj_trivial, hx, mul_comm]
    have hre (i : ι) : restrictL2 hm (R (w i)) = restrictL2 hm' (J (w i)) := by
      apply Lp.ext
      exact ((restrictL2_ae hm (R (w i))).trans (ae_mono hm
        (closedRestrict_ae H hS₁ (w i)))).trans
        ((restrictL2_ae hm' (J (w i))).trans (ae_mono hm'
          (closedRestrict_ae H hO₁ (w i)))).symm
    have hgram' (i j : ι) : inner ℝ (R (w i)) (R (w j)) =
        @ite ℝ (i = j) (Classical.propDecidable _) (μ i ^ 2) 0 := by
      by_cases h : i = j
      · simp only [ite_eq_left h]
        simpa only [ite_eq_left h] using hgram i j
      · simp only [ite_eq_right h]
        simpa only [ite_eq_right h] using hgram i j
    simpa only [hyre, ← hre, map_smul] using
      (restrictL2 hm).hasSum (hasSum_singularCoefficient_closure R μ w hμ hgram' huR)

/-- Closed-range membership of the second-arm slices follows from
scalar unique continuation and the common first-arm coefficients. -/
theorem ae_secondArm_scalar_slices_mem_rangeClosure
    {D₁ D₂ S₁ S₂ : Set (X dim)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hconn : IsConnected D₂) (hS₂ : IsOpen S₂) (hne : S₂.Nonempty)
    (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂)
    {L₁ L₂ : ScalarElliptic dim} (hL₁ : L₁.SmoothOn D₁) (hL₂ : L₂.SmoothOn D₂)
    (hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
    (q₁ : ChartProductL2 D₁ S₂) (q₂ : ChartProductL2 S₁ D₂)
    (hAgree : (q₁ : X dim × X dim → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] q₂)
    (hSlice₁ : ∀ᵐ y ∂chartMeasure S₂, ∃ u : scalarSolutionL2 hD₁ hL₁,
      (u.1 : X dim → ℝ) =ᵐ[chartMeasure D₁] fun x => q₁ (x,y))
    (hSlice₂ : ∀ᵐ x ∂chartMeasure S₁, ∃ u : scalarSolutionL2 hD₂ hL₂,
      (u.1 : X dim → ℝ) =ᵐ[chartMeasure D₂] fun y => q₂ (x,y)) :
    ∀ᵐ y ∂chartMeasure D₂,
      ∃ u ∈ closure (range (closedRestrict (scalarSolutionL2 hD₁ hL₁) hS₁D₁)),
        (u : X dim → ℝ) =ᵐ[chartMeasure S₁] fun x => q₂ (x,y) := by
  let : IsFiniteMeasure (chartMeasure D₂) := isFiniteMeasure_restrict.mpr hfinite
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let H₁ := scalarSolutionL2 hD₁ hL₁
  let H₂ := scalarSolutionL2 hD₂ hL₂
  let R := closedRestrict H₁ hS₁D₁
  let J := H₁.toSubmodule.subtypeL
  let hm := Measure.restrict_mono_set (volume : Measure (X dim)) hS₁D₁
  let hn := Measure.restrict_mono_set (volume : Measure (X dim)) hS₂D₂
  apply ae_slice_mem_rangeClosure R q₂
  intro z hz
  have hzero := restrict_tensorCoefficient_eq_zero_of_orthogonal R J hm hn (fun _ => rfl) q₁ q₂ hAgree
    hSlice₁ z (fun u => (Submodule.mem_orthogonal _ _).mp hz _ (LinearMap.mem_range_self _ u))
  let u : H₂ := ⟨_, tensorCoefficient_mem_of_slices H₂ z q₂ hSlice₂⟩
  have hEq : closedRestrict H₂ hS₂D₂ u = 0 := hzero
  have hu : u = 0 := closedRestrict_injective hD₂ hconn hL₂ hS₂ hne hS₂D₂
    (hEq.trans (map_zero _).symm)
  exact congrArg Subtype.val hu

end CalderonPaper.ScalarElliptic
