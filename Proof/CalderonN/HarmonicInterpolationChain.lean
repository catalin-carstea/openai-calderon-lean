module

public import Proof.CalderonN.HarmonicCollarInterpolation

public import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.CrossArmCoefficients
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open LocalMetricExtension (restrictL2 restrictL2_ae norm_restrictL2_le)

theorem harmonicRestrict_norm_mono {D S T : Set (X dim)} (hD : IsOpen D) {g : (MetricField dim)}
    (hg : SmoothMetric D g) (hTS : T ⊆ S) (hSD : S ⊆ D) (q : harmonicL2Space hD hg) :
    ‖harmonicRestrict hD hg (hTS.trans hSD) q‖ ≤ ‖harmonicRestrict hD hg hSD q‖ := by
  let h := Measure.restrict_mono_set (volume : Measure (X dim)) hTS
  let R := restrictL2 h
  have he : harmonicRestrict hD hg (hTS.trans hSD) q = R (harmonicRestrict hD hg hSD q) :=
    Lp.ext ((harmonicRestrict_ae hD hg (hTS.trans hSD) q).trans
      ((restrictL2_ae h (harmonicRestrict hD hg hSD q)).trans
        (ae_mono h (harmonicRestrict_ae hD hg hSD q))).symm)
  rw [he]
  have hb : ‖R‖ ≤ 1 := norm_restrictL2_le h
  calc
    ‖R (harmonicRestrict hD hg hSD q)‖ ≤ ‖R‖ * ‖harmonicRestrict hD hg hSD q‖ := R.le_opNorm _
    _ ≤ 1 * ‖harmonicRestrict hD hg hSD q‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := one_mul _

theorem harmonicRestrict_norm_le_finset_cover {ι : Type*} (f : Finset ι)
    {D T : Set (X dim)} (hD : IsOpen D) {g : (MetricField dim)} (hg : SmoothMetric D g)
    (O : ι → Set (X dim)) (hO : ∀ i, MeasurableSet (O i)) (hOD : ∀ i, O i ⊆ D)
    (hTD : T ⊆ D) (hCover : T ⊆ ⋃ i ∈ f, O i) (q : harmonicL2Space hD hg) :
    ‖harmonicRestrict hD hg hTD q‖ ≤ ∑ i ∈ f, ‖harmonicRestrict hD hg (hOD i) q‖ := by
  classical
  have hUnion (s : Finset ι) : (⋃ i ∈ s, O i) ⊆ D :=
    iUnion_subset fun i => iUnion_subset fun _ => hOD i
  refine (harmonicRestrict_norm_mono hD hg hCover (hUnion f) q).trans ?_
  clear hCover hTD T
  induction f using Finset.induction_on with
  | empty =>
      have hEmpty : harmonicRestrict hD hg (hUnion ∅) q = 0 := by
        apply Lp.ext
        simp [Filter.EventuallyEq]
      rw [hEmpty, norm_zero, Finset.sum_empty]
  | insert i f hi hrec =>
      rw [Finset.sum_insert hi]
      have hs : (⋃ j ∈ insert i f, O j) ⊆ (⋃ j ∈ f, O j) ∪ O i := by
        rw [Finset.set_biUnion_insert,union_comm]
      have hstep := harmonicRestrict_norm_le_of_subset_union hD hg (hUnion f) (hOD i)
        (hUnion (insert i f)) (hO i) hs q
      refine hstep.trans ?_
      rw [add_comm]
      exact add_le_add le_rfl hrec

theorem interpolation_product_mono_exponent {S D a b : ℝ} (hS : 0 ≤ S) (hSD : S ≤ D)
    (ha : 0 < a) (hab : a ≤ b) :
    S ^ b * D ^ (1-b) ≤ S ^ a * D ^ (1-a) := by
  by_cases hzero : S = 0
  · subst S
    simp [Real.zero_rpow (ha.trans_le hab).ne',Real.zero_rpow ha.ne']
  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
  have hDp : 0 < D := hSp.trans_le hSD
  have hform (γ : ℝ) : S ^ γ * D ^ (1-γ) = D * (S/D) ^ γ := by
    rw [Real.div_rpow hS hDp.le,Real.rpow_sub hDp,Real.rpow_one]
    ring
  rw [hform,hform]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (div_pos hSp hDp) ((div_le_one hDp).mpr hSD) hab) hDp.le

/-- An observed restriction is itself controlled by interpolation with
the original domain norm. -/
theorem observed_norm_le_interpolation {S D γ : ℝ}
    (hS : 0 ≤ S) (hSD : S ≤ D) (hγ : γ < 1) :
    S ≤ S ^ γ * D ^ (1-γ) := by
  by_cases hz : S = 0
  · subst S
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (hS.trans hSD) _)
  have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  calc
    S = S ^ γ * S ^ (1-γ) := by
      rw [← Real.rpow_add hpos,show γ+(1-γ)=1 by ring,Real.rpow_one]
    _ ≤ S ^ γ * D ^ (1-γ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hS hSD (sub_nonneg.mpr hγ.le)) (Real.rpow_nonneg hS _)

/-! The scalar composition argument is adapted from
`MixedKernelPropagationAndAnnularSeries.lean` at
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

/-- Exponent composition for the sphere step: a compact-data estimate with exponent `a`
fed into a local interpolation with exponent `b` (local full norm `Dl ≤ D`) gives exponent
`a*b`. Zero observed/full data are included; only nonnegative rpow laws are used. -/
private theorem interpolation_compose {S D T O Dl CT Cl a b : ℝ}
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hT : 0 ≤ T) (hCT : 0 ≤ CT) (hCl : 0 ≤ Cl)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hDl0 : 0 ≤ Dl) (hDl : Dl ≤ D)
    (hTb : T ≤ CT*(S^a*D^(1-a))) (hO : O ≤ Cl*(T^b*Dl^(1-b))) :
    O ≤ Cl*CT^b*(S^(a*b)*D^(1-a*b)) := by
  have hSa : 0 ≤ S^a := Real.rpow_nonneg hS _
  have hDa : 0 ≤ D^(1-a) := Real.rpow_nonneg hD _
  have h1 : T^b ≤ (CT*(S^a*D^(1-a)))^b := Real.rpow_le_rpow hT hTb hb0.le
  have h2 : Dl^(1-b) ≤ D^(1-b) := Real.rpow_le_rpow hDl0 hDl (by linarith)
  have hab : a*b < 1 := by nlinarith
  have hne : (1-a)*b+(1-b) ≠ 0 := by
    have he : (1-a)*b+(1-b) = 1-a*b := by ring
    rw [he]
    linarith
  have hDexp : D^((1-a)*b)*D^(1-b) = D^(1-a*b) := by
    rw [← Real.rpow_add' hD hne]
    congr 1
    ring
  calc O ≤ Cl*(T^b*Dl^(1-b)) := hO
    _ ≤ Cl*((CT*(S^a*D^(1-a)))^b*D^(1-b)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h1 h2 (Real.rpow_nonneg hDl0 _) (Real.rpow_nonneg (by positivity) _)) hCl
    _ = Cl*CT^b*(S^(a*b)*D^(1-a*b)) := by
      rw [Real.mul_rpow hCT (mul_nonneg hSa hDa), Real.mul_rpow hSa hDa,
        ← Real.rpow_mul hS, ← Real.rpow_mul hD, ← hDexp]
      ring

/-- An interpolation step inside a smaller domain composes with a bound
from the original observation. The exponents multiply. -/
theorem HarmonicInterpolation.comp_of_subset
    {D U S T O : Set (X dim)} (hD : IsOpen D) (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric D g) (hUD : U ⊆ D) (hSD : S ⊆ D) (hTU : T ⊆ U) (hOU : O ⊆ U)
    {C₁ C₂ α β : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (h₁ : HarmonicInterpolation hD hg hSD (hTU.trans hUD) C₁ α)
    (h₂ : HarmonicInterpolation hU (smoothMetric_restrict hg hUD) hTU hOU C₂ β) :
    HarmonicInterpolation hD hg hSD (hOU.trans hUD) (C₂*C₁^β) (α*β) := by
  intro q
  let u : harmonicL2Space hU (smoothMetric_restrict hg hUD) :=
    ⟨harmonicRestrict hD hg hUD q,harmonicRestrict_mem hD hU hg hUD q⟩
  have heq (V : Set (X dim)) (hVU : V ⊆ U) :
      harmonicRestrict hU (smoothMetric_restrict hg hUD) hVU u =
        harmonicRestrict hD hg (hVU.trans hUD) q := by
    apply Lp.ext
    have hmid : (u.1 : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict V] (q.1 : (X dim) → ℝ) :=
      ae_mono (Measure.restrict_mono_set volume hVU) (harmonicRestrict_ae hD hg hUD q)
    exact (harmonicRestrict_ae hU (smoothMetric_restrict hg hUD) hVU u).trans
      (hmid.trans (harmonicRestrict_ae hD hg (hVU.trans hUD) q).symm)
  have hb := h₂ u
  rw [heq O hOU,heq T hTU] at hb
  have hUle : ‖u‖ ≤ ‖q‖ := harmonicRestrict_norm_le hD hg hUD q
  simpa only [mul_assoc] using interpolation_compose
    (norm_nonneg _) (norm_nonneg q) (norm_nonneg _) hC₁ hC₂ hα hα1 hβ hβ1 (norm_nonneg u) hUle
    (by simpa only [mul_assoc] using h₁ q) (by simpa only [mul_assoc] using hb)

end CalderonN
