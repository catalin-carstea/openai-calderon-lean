module

public import Proof.CalderonN.CrossRangeClosure
public import Proof.CalderonN.CrossSeries

import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.SeparableMeasure

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension

theorem harmonicRestrict_injective
    {D S : Set (X dim)} (hD : IsOpen D) (hc : IsConnected D) (hS : IsOpen S) (hne : S.Nonempty)
    (hSD : S ⊆ D) {g : (MetricField dim)} (hg : SmoothMetric D g) :
    Function.Injective (harmonicRestrict hD hg hSD) := by
  intro u v huv
  obtain ⟨f, hf, hfu⟩ := harmonicL2Space_representative hD hg u
  obtain ⟨k, hk, hkv⟩ := harmonicL2Space_representative hD hg v
  have hDdom := Measure.restrict_mono_set (volume : Measure (X dim)) hSD
  have hae : f =ᵐ[(volume : Measure (X dim)).restrict S] k := by
    calc
      f =ᵐ[(volume : Measure (X dim)).restrict S] (u.1 : (X dim) → ℝ) :=
        Filter.EventuallyEq.symm (ae_mono hDdom hfu)
      _ =ᵐ[(volume : Measure (X dim)).restrict S] (harmonicRestrict hD hg hSD u : (X dim) → ℝ) :=
        (harmonicRestrict_ae hD hg hSD u).symm
      _ =ᵐ[(volume : Measure (X dim)).restrict S] (v.1 : (X dim) → ℝ) :=
        huv ▸ harmonicRestrict_ae hD hg hSD v
      _ =ᵐ[(volume : Measure (X dim)).restrict S] k := ae_mono hDdom hkv
  have hfks := Measure.eqOn_open_of_ae_eq hae hS
    (hf.1.continuousOn.mono hSD) (hk.1.continuousOn.mono hSD)
  have hfkd := harmonic_eqOn_of_eqOn_open hD hc hS hne hSD hg hf hk hfks
  have hfd : f =ᵐ[(volume : Measure (X dim)).restrict D] k :=
    (ae_restrict_mem hD.measurableSet).mono fun x hx => hfkd hx
  exact Subtype.ext (Lp.ext (hfu.trans (hfd.trans hkv.symm)))

private abbrev chartMeasure (D : Set (X dim)) : Measure (X dim) := (volume : Measure (X dim)).restrict D

/-- The second-arm slices belong to the closed restriction range, using
the classical harmonic representatives and scalar unique continuation. -/
theorem ae_secondArm_slices_mem_rangeClosure
    {D₁ D₂ S₁ S₂ : Set (X dim)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hconn : IsConnected D₂) (hS₁ : MeasurableSet S₁) (hS₂ : IsOpen S₂) (hne : S₂.Nonempty)
    (hS₁D₁ : S₁ ⊆ D₁) (hS₂D₂ : S₂ ⊆ D₂)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric D₁ g₁) (hg₂ : SmoothMetric D₂ g₂)
    (hfinite : (volume : Measure (X dim)) D₂ ≠ ⊤)
    (q₁ : ChartProductL2 (d := dim) D₁ S₂) (q₂ : ChartProductL2 (d := dim) S₁ D₂) {F : (X dim) × (X dim) → ℝ}
    (hq₁ : (q₁ : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict D₁).prod
      ((volume : Measure (X dim)).restrict S₂)] F)
    (hq₂ : (q₂ : (X dim) × (X dim) → ℝ) =ᵐ[((volume : Measure (X dim)).restrict S₁).prod
      ((volume : Measure (X dim)).restrict D₂)] F)
    (hF₁ : ∀ y ∈ S₂, Harmonic D₁ g₁ (fun x => F (x,y)))
    (hF₂ : ∀ x ∈ S₁, Harmonic D₂ g₂ (fun y => F (x,y))) :
    ∀ᵐ y ∂(volume : Measure (X dim)).restrict D₂,
      ∃ u ∈ closure (range (harmonicRestrict hD₁ hg₁ hS₁D₁)),
        (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict S₁] fun x => q₂ (x,y) := by
  let : IsFiniteMeasure (chartMeasure D₂) := isFiniteMeasure_restrict.mpr hfinite
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let R := harmonicRestrict hD₁ hg₁ hS₁D₁
  let J := (harmonicL2Space hD₁ hg₁).toSubmodule.subtypeL
  let hm := Measure.restrict_mono_set (volume : Measure (X dim)) hS₁D₁
  let hn := Measure.restrict_mono_set (volume : Measure (X dim)) hS₂D₂
  have hR (u : harmonicL2Space hD₁ hg₁) : R u = restrictL2 hm (J u) :=
    Lp.ext ((harmonicRestrict_ae hD₁ hg₁ hS₁D₁ u).trans (restrictL2_ae hm (J u)).symm)
  have hagree : (q₁ : (X dim) × (X dim) → ℝ) =ᵐ[(chartMeasure S₁).prod (chartMeasure S₂)] q₂ :=
    Filter.EventuallyEq.trans (ae_mono (Measure.prod_mono hm le_rfl) hq₁)
      (Filter.EventuallyEq.symm (ae_mono (Measure.prod_mono le_rfl hn) hq₂))
  apply ae_slice_mem_rangeClosure R q₂
  intro z hz
  have hzero := restrict_tensorCoefficient_eq_zero_of_orthogonal R J hm hn hR q₁ q₂ hagree
    (ae_firstArm_slices hD₁ hS₂.measurableSet hg₁ hq₁ hF₁) z
    (fun u => (Submodule.mem_orthogonal _ _).mp hz _ (LinearMap.mem_range_self _ u))
  have hweak := tensorCoefficient_mem_harmonicL2Space hS₁ hD₂ hg₂ z q₂ hq₂ hF₂
  let u : harmonicL2Space hD₂ hg₂ := ⟨_, hweak⟩
  have hre : harmonicRestrict hD₂ hg₂ hS₂D₂ u = 0 :=
    (Lp.ext ((harmonicRestrict_ae hD₂ hg₂ hS₂D₂ u).trans
      (restrictL2_ae hn (tensorCoefficient z q₂)).symm)).trans hzero
  have hu : u = 0 := harmonicRestrict_injective hD₂ hconn hS₂ hne hS₂D₂ hg₂
    (hre.trans (map_zero _).symm)
  exact congrArg Subtype.val hu

end CalderonN
