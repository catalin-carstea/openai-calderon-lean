module

public import Proof.CalderonN.HarmonicL2Series

import Proof.CalderonN.DilationHarmonic
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {d : ℕ} [NeZero d]

theorem laplace_sub {U : Set (X d)} (hU : IsOpen U) (g : (MetricField d)) {u v : (X d) → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U) {x : (X d)} (hx : x ∈ U) :
    laplace g (fun z => u z - v z) x = laplace g u x - laplace g v x := by
  have hu' := (hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hv' := (hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hd (i : (I d)) : coordDeriv i (fun z => u z - v z) x = coordDeriv i u x - coordDeriv i v x := by
    simp only [coordDeriv, fderiv_fun_sub hu' hv', sub_apply]
  have hh (i j : (I d)) : coordDeriv i (coordDeriv j (fun z => u z - v z)) x =
      coordDeriv i (coordDeriv j u) x - coordDeriv i (coordDeriv j v) x :=
    by
      have hEq : coordDeriv j (fun z => u z - v z) =ᶠ[𝓝 x]
          (fun z => coordDeriv j u z - coordDeriv j v z) := by
        filter_upwards [hU.mem_nhds hx] with z hz
        have hzu := (hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
        have hzv := (hv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
        simp only [coordDeriv, fderiv_fun_sub hzu hzv, sub_apply]
      have hdu := (hu.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply
        (contDiffOn_const (c := axis j))
      have hdv := (hv.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply
        (contDiffOn_const (c := axis j))
      change fderiv ℝ (coordDeriv j (fun z => u z - v z)) x (axis i) =
        fderiv ℝ (coordDeriv j u) x (axis i) - fderiv ℝ (coordDeriv j v) x (axis i)
      rw [show fderiv ℝ (coordDeriv j (fun z => u z - v z)) x =
          fderiv ℝ (fun z => coordDeriv j u z - coordDeriv j v z) x from hEq.fderiv_eq,
        fderiv_fun_sub (f := coordDeriv j u) (g := coordDeriv j v)
          ((hdu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx))
          ((hdv.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)), sub_apply]
  simp only [laplace, hd, hh, mul_sub, Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Harmonic.sub {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)} {u v : (X d) → ℝ}
    (hu : Harmonic U g u) (hv : Harmonic U g v) :
    Harmonic U g (fun z => u z - v z) :=
  ⟨hu.1.sub hv.1, fun x hx => by rw [laplace_sub hU g hu.1 hv.1 hx, hu.2 x hx, hv.2 x hx, sub_self]⟩

/-- An L² class represented by a classical harmonic function on the chart. -/
@[expose] def HasHarmonicRepresentative (U : Set (X d)) (g : (MetricField d)) (u : ChartL2 (d := d) U) : Prop :=
  ∃ f : (X d) → ℝ, Harmonic U g f ∧ (u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f

private theorem harmonic_const_mul {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    {f : (X d) → ℝ} (hf : Harmonic U g f) (c : ℝ) :
    Harmonic U g (fun x => c*f x) :=
  ⟨contDiffOn_const.mul hf.1,fun x hx => by
    rw [laplace_const_mul hU hf.1 hx g, hf.2 x hx, mul_zero]⟩

private theorem harmonic_add {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    {f k : (X d) → ℝ} (hf : Harmonic U g f) (hk : Harmonic U g k) :
    Harmonic U g (fun x => f x + k x) := by
  simpa only [neg_one_mul,sub_neg_eq_add] using hf.sub hU (harmonic_const_mul hU hk (-1))

private theorem representative_add {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    {u v : ChartL2 (d := d) U} (hu : HasHarmonicRepresentative U g u)
    (hv : HasHarmonicRepresentative U g v) : HasHarmonicRepresentative U g (u+v) := by
  obtain ⟨f,hf,huf⟩ := hu
  obtain ⟨k,hk,hvk⟩ := hv
  exact ⟨fun x => f x + k x,harmonic_add hU hf hk,(Lp.coeFn_add u v).trans (huf.add hvk)⟩

/-- The smooth harmonic classes themselves form a closed subspace.
A rapidly convergent subsequence produces an absolutely summable
telescoping series of smooth harmonic differences. -/
theorem isClosed_hasHarmonicRepresentative {U : Set (X d)} (hU : IsOpen U)
    {g : (MetricField d)} (hg : SmoothMetric U g) :
    IsClosed {u : ChartL2 (d := d) U | HasHarmonicRepresentative U g u} := by
  classical
  apply closure_subset_iff_isClosed.mp
  intro u hu
  obtain ⟨w,hw,hwlim⟩ := mem_closure_iff_seq_limit.mp hu
  obtain ⟨a,ha,hs⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq w hwlim.cauchySeq
  let b (n : ℕ) := w (a n)
  let v (n : ℕ) := b (n+1)-b n
  have hb : Tendsto b atTop (𝓝 u) := hwlim.comp ha.tendsto_atTop
  have hAbs : Summable (fun n : ℕ => ‖v n‖) := by
    simpa only [v,b,dist_eq_norm,norm_sub_rev] using hs
  have hsum : HasSum v (u-b 0) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm hAbs).mpr
    have htel : (fun n => ∑ j ∈ Finset.range n, v j) = fun n => b n-b 0 := by
      funext n
      exact Finset.sum_range_sub b n
    rw [htel]
    exact hb.sub_const (b 0)
  choose f hf hEq using fun n => hw (a n)
  have hDiff (n : ℕ) : Harmonic U g (fun x => f (n+1) x - f n x) :=
    (hf (n+1)).sub hU (hf n)
  have hDiffEq (n : ℕ) :
      (v n : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] fun x => f (n+1) x - f n x :=
    (Lp.coeFn_sub (b (n+1)) (b n)).trans ((hEq (n+1)).sub (hEq n))
  obtain ⟨F,hF,hRep⟩ := exists_harmonic_representative_of_hasSum hU hg v _
    hDiff hDiffEq hAbs hsum
  have h0 : HasHarmonicRepresentative U g (b 0) := ⟨f 0,hf 0,hEq 0⟩
  have hfinal := representative_add hU (show HasHarmonicRepresentative U g (u-b 0) from ⟨F,hF,hRep⟩) h0
  change HasHarmonicRepresentative U g u
  simpa only [sub_add_cancel] using hfinal

/-- The Hilbert space of classical harmonic L² classes. -/
def harmonicL2Space {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)} (hg : SmoothMetric U g) :
    ClosedSubmodule ℝ (ChartL2 (d := d) U) where
  carrier := {u | HasHarmonicRepresentative U g u}
  zero_mem' := by
    refine ⟨fun _ => 0,⟨contDiffOn_const,fun x hx => ?_⟩,Lp.coeFn_zero _ _ _⟩
    have h : ContDiffOn ℝ ∞ (fun _ : (X d) => (1 : ℝ)) U := contDiffOn_const
    simpa only [zero_mul] using laplace_const_mul hU h hx g 0
  add_mem' := fun h₁ h₂ => representative_add hU h₁ h₂
  smul_mem' c u hu := by
    obtain ⟨f,hf,hEq⟩ := hu
    exact ⟨fun x => c*f x, harmonic_const_mul hU hf c,
      (Lp.coeFn_smul c u).trans (hEq.const_smul c)⟩
  isClosed' := isClosed_hasHarmonicRepresentative hU hg

theorem mem_harmonicL2Space_iff {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) (u : ChartL2 (d := d) U) :
    u ∈ harmonicL2Space hU hg ↔ HasHarmonicRepresentative U g u := Iff.rfl

theorem harmonicL2Space_representative {U : Set (X d)} (hU : IsOpen U)
    {g : (MetricField d)} (hg : SmoothMetric U g) (u : harmonicL2Space hU hg) :
    HasHarmonicRepresentative U g u.1 :=
  (mem_harmonicL2Space_iff hU hg u.1).mp u.2

theorem harmonic_mem_harmonicL2Space {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {f : (X d) → ℝ} (hf : Harmonic U g f)
    (hfLp : MemLp f 2 ((volume : Measure (X d)).restrict U)) :
    hfLp.toLp f ∈ harmonicL2Space hU hg :=
  (mem_harmonicL2Space_iff hU hg _).mpr ⟨f,hf,hfLp.coeFn_toLp⟩

/-- Testing a classical harmonic representative gives the original weak
equation for its entire L² class. -/
theorem harmonicL2Space_le_weakHarmonicL2Space {U : Set (X d)} (hU : IsOpen U)
    {g : (MetricField d)} (hg : SmoothMetric U g) :
    harmonicL2Space hU hg ≤ weakHarmonicL2Space hU hg := by
  intro u hu
  obtain ⟨f,hf,hRep⟩ := (mem_harmonicL2Space_iff hU hg u).mp hu
  apply (mem_weakHarmonicL2Space_iff hU hg u).mpr
  intro φ
  refine (integral_congr_ae ?_).trans (integral_harmonic_test_eq_zero hU hg hf φ)
  filter_upwards [hRep] with x hx
  rw [hx]

/-- Restriction from the closed space of classical harmonic representatives. -/
@[expose] def harmonicRestrict {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {V : Set (X d)} (hVU : V ⊆ U) :
    harmonicL2Space hU hg →L[ℝ] ChartL2 (d := d) V :=
  (Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono_set volume hVU)).comp
    (harmonicL2Space hU hg).toSubmodule.subtypeL

theorem harmonicRestrict_ae {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {V : Set (X d)} (hVU : V ⊆ U) (u : harmonicL2Space hU hg) :
    (harmonicRestrict hU hg hVU u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict V] (u.1 : (X d) → ℝ) :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (by simpa only [one_smul] using Measure.restrict_mono_set volume hVU) u.1

end CalderonN
