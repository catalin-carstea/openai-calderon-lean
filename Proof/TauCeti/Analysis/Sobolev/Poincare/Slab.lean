/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
 
 
 
public import Proof.TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod

 












































public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped ENNReal Topology

section OneDimensional

variable {F : Type*} [NormedAddCommGroup F] {g : ℝ → F} {a b : ℝ}

 

private theorem eq_zero_of_support_subset_Icc (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc a b) : g a = 0 := by
  refine tendsto_nhds_unique (f := g) (l := 𝓝[<] a) hg.continuousAt.continuousWithinAt.tendsto ?_
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  by_contra h
  exact absurd (hsupp (Function.mem_support.2 fun h' => h h'.symm)).1 (not_le.2 ht)

 

private theorem eq_zero_of_support_subset_Icc_self (hsupp : Function.support g ⊆ Icc a a)
    (hga : g a = 0) (t : ℝ) : g t = 0 := by
  by_cases h : g t = 0
  · exact h
  · have htm := hsupp (Function.mem_support.2 h)
    rw [le_antisymm htm.2 htm.1]
    exact hga

 

private theorem support_enorm_rpow_subset_Ioc (hsupp : Function.support g ⊆ Icc a b)
    (hga : g a = 0) {r : ℝ} (hr0 : 0 < r) :
    Function.support (fun t => ‖g t‖ₑ ^ r) ⊆ Ioc a b := by
  intro t ht
  have hgt : g t ≠ 0 := fun h => ht (by simp [h, ENNReal.zero_rpow_of_pos hr0])
  have htm := hsupp (Function.mem_support.2 hgt)
  exact ⟨htm.1.lt_of_ne fun h => hgt (h ▸ hga), htm.2⟩

variable [NormedSpace ℝ F] {g' : ℝ → F}

 





private theorem enorm_le_lintegral_enorm_deriv
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g') (hga : g a = 0)
    {t : ℝ} (ht : t ∈ Icc a b) : ‖g t‖ₑ ≤ ∫⁻ s in Ioc a b, ‖g' s‖ₑ := by
   
   
  have hderiv : deriv g = g' := funext fun x => (hg x).deriv
  have hC1 : ContDiff ℝ 1 g :=
    contDiff_one_iff_deriv.2 ⟨fun x => (hg x).differentiableAt, hderiv ▸ hg'⟩
  calc ‖g t‖ₑ = ‖g t - g a‖ₑ := by rw [hga, sub_zero]
    _ ≤ ∫⁻ s in Icc a t, ‖deriv g s‖ₑ :=
        enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hC1.contDiffOn ht.1
    _ = ∫⁻ s in Ioc a t, ‖g' s‖ₑ := by rw [hderiv, setLIntegral_congr Ioc_ae_eq_Icc]
    _ ≤ ∫⁻ s in Ioc a b, ‖g' s‖ₑ := lintegral_mono_set (Ioc_subset_Ioc_right ht.2)

 









theorem lintegral_enorm_rpow_le_of_support_subset_Icc (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (hsupp : Function.support g ⊆ Icc a b) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ t, ‖g t‖ₑ ^ r ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖g' t‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hga : g a = 0 := eq_zero_of_support_subset_Icc hgc hsupp
   
  rcases hab.eq_or_lt with rfl | hab'
  · simp [eq_zero_of_support_subset_Icc_self hsupp hga, ENNReal.zero_rpow_of_pos hr0]
  have hba : (0 : ℝ) < b - a := sub_pos.2 hab'
  have hpow : ENNReal.ofReal (b - a) ^ (r - 1) * ENNReal.ofReal (b - a)
      = ENNReal.ofReal ((b - a) ^ r) := by
    nth_rewrite 2 [← ENNReal.rpow_one (ENNReal.ofReal (b - a))]
    have hsum : r - 1 + 1 = r := by ring
    rw [← ENNReal.rpow_add _ _ (by simpa using hba) ENNReal.ofReal_ne_top, hsum,
      ENNReal.ofReal_rpow_of_pos hba]
  calc ∫⁻ t, ‖g t‖ₑ ^ r
      = ∫⁻ t in Ioc a b, ‖g t‖ₑ ^ r :=
        (setLIntegral_eq_of_support_subset (support_enorm_rpow_subset_Ioc hsupp hga hr0)).symm
    _ ≤ ∫⁻ _ in Ioc a b, (∫⁻ s in Ioc a b, ‖g' s‖ₑ) ^ r := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact ENNReal.rpow_le_rpow
          (enorm_le_lintegral_enorm_deriv hg hg' hga (Ioc_subset_Icc_self ht)) hr0.le
    _ = (∫⁻ s in Ioc a b, ‖g' s‖ₑ) ^ r * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ ≤ (ENNReal.ofReal (b - a) ^ (r - 1) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r) *
          ENNReal.ofReal (b - a) := by
        gcongr
        have hmu : (volume.restrict (Ioc a b)) Set.univ = ENNReal.ofReal (b - a) := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        simpa only [hmu] using rpow_lintegral_le_measure_univ_rpow_mul
          (μ := volume.restrict (Ioc a b)) hg'.enorm.measurable.aemeasurable hr
    _ = ENNReal.ofReal ((b - a) ^ r) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r := by
        rw [mul_right_comm, hpow]
    _ ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖g' t‖ₑ ^ r :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

 




theorem eLpNorm_le_eLpNorm_deriv_of_support_subset_Icc (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (hsupp : Function.support g ⊆ Icc a b) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm g p volume ≤ ENNReal.ofReal (b - a) * eLpNorm g' p volume :=
  eLpNorm_le_eLpNorm_of_lintegral_rpow_le (sub_nonneg.2 hab) (zero_lt_one.trans_le hp).ne' hp'
    ((continuous_iff_continuousAt.2 fun t => (hg t).continuousAt).aestronglyMeasurable)
    (lintegral_enorm_rpow_le_of_support_subset_Icc hab hg hg' hsupp
      (by simpa using ENNReal.toReal_mono hp' hp))

end OneDimensional

section Slab

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1)) → F} {i : Fin (n + 1)} {a b : ℝ}

 

private def slabChart (i : Fin (n + 1)) (z : ℝ × (Fin n → ℝ)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (i.insertNth z.1 z.2)

@[simp]
private theorem slabChart_apply_same (z : ℝ × (Fin n → ℝ)) : slabChart i z i = z.1 := by
  simp [slabChart]

 

private theorem slabChart_eq_add_smul_single (y : Fin n → ℝ) (t : ℝ) :
    slabChart i (t, y) =
      WithLp.toLp 2 (i.insertNth (0 : ℝ) y) + t • EuclideanSpace.single i (1 : ℝ) := by
  have hpi : i.insertNth t y = i.insertNth (0 : ℝ) y + t • Pi.single i (1 : ℝ) := by
    funext j
    refine Fin.succAboveCases i ?_ ?_ j <;> simp
  simp [slabChart, hpi]

 
private theorem measurePreserving_slabChart :
    MeasurePreserving (slabChart i) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n + 1) → ℝ)) := by
    simpa [volume_pi] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i).symm
  exact (PiLp.volume_preserving_toLp (Fin (n + 1))).comp h1

 
private theorem lintegral_eq_lintegral_slabChart {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞}
    (hw : Measurable w) : ∫⁻ x, w x = ∫⁻ y, ∫⁻ t, w (slabChart i (t, y)) := by
  rw [← (measurePreserving_slabChart (i := i)).lintegral_comp hw]
  exact lintegral_prod_symm (fun z => w (slabChart i z))
    (hw.comp (measurePreserving_slabChart (i := i)).measurable).aemeasurable

 


private theorem hasDerivAt_comp_slabChart (y : Fin n → ℝ) {t : ℝ}
    (hu : DifferentiableAt ℝ u (slabChart i (t, y))) :
    HasDerivAt (fun s => u (slabChart i (s, y)))
      (fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1)) t := by
  have hl : HasDerivAt (fun s : ℝ => slabChart i (s, y)) (EuclideanSpace.single i 1) t := by
    simp only [slabChart_eq_add_smul_single]
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    simpa using _root_.HasDerivAt.const_add (WithLp.toLp 2 (i.insertNth (0 : ℝ) y))
      (_root_.HasDerivAt.smul_const hid (EuclideanSpace.single i (1 : ℝ)))
  exact hu.hasFDerivAt.comp_hasDerivAt t hl

 



private theorem lintegral_enorm_rpow_comp_slabChart_le {y : Fin n → ℝ}
    (hu : ∀ t : ℝ, DifferentiableAt ℝ u (slabChart i (t, y)))
    (hfc : Continuous fun t : ℝ => fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1))
    (hab : a ≤ b) (hsupp : Function.support (fun t : ℝ => u (slabChart i (t, y))) ⊆ Icc a b)
    {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r
      ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r := by
  refine le_trans (lintegral_enorm_rpow_le_of_support_subset_Icc hab
    (fun t => hasDerivAt_comp_slabChart y (hu t)) hfc hsupp hr) ?_
  gcongr with t
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using (fderiv ℝ u (slabChart i (t, y))).le_opNorm (EuclideanSpace.single i 1)

 









theorem eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab (hu : ContDiff ℝ 1 u) (hab : a ≤ b)
    (hsupp : ∀ x ∈ Function.support u, x i ∈ Icc a b) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm u p volume ≤ ENNReal.ofReal (b - a) * eLpNorm (fderiv ℝ u) p volume := by
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  refine eLpNorm_le_eLpNorm_of_lintegral_rpow_le (sub_nonneg.2 hab)
    (zero_lt_one.trans_le hp).ne' hp' hu.continuous.aestronglyMeasurable ?_
  set r := p.toReal
  have hmu : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖u x‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp hu.continuous.enorm).measurable
  have hmf : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖fderiv ℝ u x‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp hfc.enorm).measurable
  have hline : ∀ y : Fin n → ℝ, ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r
      ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r := fun y =>
    lintegral_enorm_rpow_comp_slabChart_le
      (fun _ => (hu.differentiable one_ne_zero).differentiableAt)
      (((hfc.comp (by simp only [slabChart_eq_add_smul_single]; fun_prop)).clm_apply
        continuous_const)) hab
      (fun t ht => by simpa using hsupp _ (Function.mem_support.2 ht)) hr
  calc ∫⁻ x, ‖u x‖ₑ ^ r
      = ∫⁻ y, ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r := lintegral_eq_lintegral_slabChart hmu
    _ ≤ ∫⁻ y, ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r :=
        lintegral_mono hline
    _ = ENNReal.ofReal ((b - a) ^ r) *
          ∫⁻ y, ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = ENNReal.ofReal ((b - a) ^ r) * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r := by
        rw [lintegral_eq_lintegral_slabChart hmf]

 
theorem apply_mem_Icc_of_mem_ball {c x : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hx : x ∈ Metric.ball c R) (i : Fin (n + 1)) : x i ∈ Icc (c i - R) (c i + R) := by
  have hnorm : ‖x - c‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hi := (PiLp.norm_apply_le (x - c) i).trans hnorm.le
  rw [Real.norm_eq_abs, WithLp.ofLp_sub, Pi.sub_apply, abs_le] at hi
  constructor <;> linarith

 






theorem eLpNorm_le_eLpNorm_fderiv_of_support_subset_ball
    {c : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hu : ContDiff ℝ 1 u)
    (hsupp : Function.support u ⊆ Metric.ball c R) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm u p volume ≤ ENNReal.ofReal (2 * R) * eLpNorm (fderiv ℝ u) p volume := by
  rcases le_or_gt R 0 with hR | hR
  · rw [Metric.ball_eq_empty.2 hR, subset_empty_iff, Function.support_eq_empty_iff] at hsupp
    simp [hsupp]
  have hslab : ∀ x ∈ Function.support u,
      x (0 : Fin (n + 1)) ∈ Icc (c 0 - R) (c 0 + R) :=
    fun x hx => apply_mem_Icc_of_mem_ball (hsupp hx) 0
  have hwidth : (c 0 + R) - (c 0 - R) = 2 * R := by ring
  simpa [hwidth] using
    eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab hu
      (by linarith : c 0 - R ≤ c 0 + R) hslab hp hp'

end Slab

end TauCeti
