module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.MetricVolumeDifferential
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

import Proof.CalderonN.GreenWeak
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.OpenPos

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {d : ℕ}

abbrev ChartL2 (U : Set (X d)) := Lp ℝ 2 ((volume : Measure (X d)).restrict U)

structure ChartTest (U : Set (X d)) where
  toFun : (X d) → ℝ
  smooth : ContDiff ℝ ∞ toFun
  compactSupport : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ U

theorem test_laplace_memLp {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) (φ : ChartTest U) :
    MemLp (fun x => chartVolume g x * laplace g φ.toFun x) 2 ((volume : Measure (X d)).restrict U) := by
  obtain ⟨hs, hc, _⟩ := density_times_laplace_of_compact_test hU hg φ.smooth φ.compactSupport φ.support_subset
  exact (hs.continuous.memLp_of_hasCompactSupport hc).restrict U

/-- The actual weighted distributional equation is a closed Hilbert
subspace, obtained by testing against the coordinate Laplacian. -/
def weakHarmonicL2Space {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)} (hg : SmoothMetric U g) :
    ClosedSubmodule ℝ (ChartL2 (d := d) U) :=
  let L (φ : ChartTest U) : ChartL2 (d := d) U →L[ℝ] ℝ :=
    innerSL ℝ ((test_laplace_memLp hU hg φ).toLp _)
  ⟨⨅ φ, (L φ).ker, by
    change IsClosed {u | u ∈ ⨅ φ, (L φ).ker}
    have he : {u | u ∈ ⨅ φ, (L φ).ker} = ⋂ φ : ChartTest U, (L φ) ⁻¹' {0} := by
      ext u
      simp only [mem_ofPred_eq, Submodule.mem_iInf, mem_iInter, mem_preimage,
        LinearMap.mem_ker, ContinuousLinearMap.coe_coe, mem_singleton_iff]
    rw [he]
    exact isClosed_iInter fun φ => isClosed_singleton.preimage (L φ).continuous⟩

theorem mem_weakHarmonicL2Space_iff {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) (u : ChartL2 (d := d) U) :
    u ∈ weakHarmonicL2Space hU hg ↔ ∀ φ : ChartTest U,
      (∫ x in U, u x * (chartVolume g x * laplace g φ.toFun x)) = 0 := by
  change (u ∈ ⨅ φ : ChartTest U, (innerSL ℝ ((test_laplace_memLp hU hg φ).toLp _)).ker) ↔ _
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
  apply forall_congr'
  intro φ
  have he : inner ℝ ((test_laplace_memLp hU hg φ).toLp _) u =
      ∫ x in U, u x * (chartVolume g x * laplace g φ.toFun x) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(test_laplace_memLp hU hg φ).coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply, conj_trivial]
  rw [he]

theorem integral_harmonic_test_eq_zero {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {f : (X d) → ℝ} (hf : Harmonic U g f) (φ : ChartTest U) :
    (∫ x in U, f x * (chartVolume g x * laplace g φ.toFun x)) = 0 := by
  calc
    _ = ∫ x in U, f x * laplace g φ.toFun x * chartVolume g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; ring
    _ = ∫ x, f x * laplace g φ.toFun x * chartVolume g x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have h := density_times_laplace_of_compact_test hU hg φ.smooth φ.compactSupport φ.support_subset
      have hz : chartVolume g x * laplace g φ.toFun x = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun z => chartVolume g z * laplace g φ.toFun z)
          (fun h' => hx (φ.support_subset (h.2.2 h')))
      rw [mul_right_comm, mul_assoc, hz, mul_zero]
    _ = ∫ x, φ.toFun x * (chartVolume g x * laplace g f x) :=
      integral_laplace_symmetric_of_compact_test hU hg hf.1 φ.smooth φ.compactSupport φ.support_subset
    _ = 0 := by
      rw [← integral_zero (α := (X d)) (G := ℝ) (μ := volume)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ U
        · simp [hf.2 x hx]
        · simp [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.support_subset h))]

theorem classical_harmonic_mem_weakSpace {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {f : (X d) → ℝ} (hf : Harmonic U g f)
    (hfLp : MemLp f 2 ((volume : Measure (X d)).restrict U)) :
    hfLp.toLp f ∈ weakHarmonicL2Space hU hg := by
  apply (mem_weakHarmonicL2Space_iff hU hg _).mpr
  intro φ
  refine (integral_congr_ae ?_).trans (integral_harmonic_test_eq_zero hU hg hf φ)
  filter_upwards [hfLp.coeFn_toLp] with x hx
  rw [hx]

/-- Restriction keeps the actual solution space as its domain. -/
@[expose] def weakHarmonicRestrict {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {V : Set (X d)} (hVU : V ⊆ U) :
    weakHarmonicL2Space hU hg →L[ℝ] ChartL2 (d := d) V :=
  (Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using Measure.restrict_mono_set volume hVU)).comp
    (weakHarmonicL2Space hU hg).toSubmodule.subtypeL

theorem weakHarmonicRestrict_ae {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)}
    (hg : SmoothMetric U g) {V : Set (X d)} (hVU : V ⊆ U) (u : weakHarmonicL2Space hU hg) :
    (weakHarmonicRestrict hU hg hVU u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict V] (u.1 : (X d) → ℝ) :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (by simpa only [one_smul] using Measure.restrict_mono_set volume hVU) u.1

end CalderonN
