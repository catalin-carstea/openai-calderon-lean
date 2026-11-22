module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Connected.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal

namespace CalderonPatch

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  {μ : Measure M} [IsFiniteMeasure μ]

private theorem sq_add_le_twice (a b : ℝ) : (a + b)^2 ≤ 2 * (a^2 + b^2) := by
  nlinarith [sq_nonneg (a - b)]

omit [TopologicalSpace M] [OpensMeasurableSpace M] in
private theorem integrable_sq_sub_const {u : M → ℝ} (hu : AEMeasurable u μ)
    (hu₂ : Integrable (fun x => (u x)^2) μ) (c : ℝ) :
    Integrable (fun x => (u x - c)^2) μ := by
  refine ((hu₂.add (integrable_const ((-c)^2))).const_mul (2 : ℝ)).mono'
    ((hu.sub aemeasurable_const).pow_const _).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (sq_nonneg _),sub_eq_add_neg]
  exact sq_add_le_twice _ _

omit [TopologicalSpace M] [OpensMeasurableSpace M] [IsFiniteMeasure μ] in
private theorem integral_sq_le_twice {a b : M → ℝ} {V : Set M} (hV : MeasurableSet V)
    (ha : IntegrableOn (fun x => (a x)^2) V μ) (hb : IntegrableOn (fun x => (b x)^2) V μ)
    {f : M → ℝ} (hEq : EqOn f (a + b) V) :
    (∫ x in V, (f x)^2 ∂μ) ≤
      2 * ((∫ x in V, (a x)^2 ∂μ) + ∫ x in V, (b x)^2 ∂μ) := by
  rw [← integral_add ha hb, ← integral_const_mul]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    ((ha.add hb).const_mul 2)
  filter_upwards [ae_restrict_mem hV] with x hx
  rw [hEq hx,Pi.add_apply]
  exact sq_add_le_twice _ _

/-- A Poincaré estimate relative to a local constant and an absolute
estimate on an overlapping open set give an absolute estimate on
the entire local set. -/
private theorem integral_sq_le_of_open_overlap [μ.IsOpenPosMeasure]
    {V W : Set M} (hV : IsOpen V) (hW : IsOpen W) (hO : (V ∩ W).Nonempty)
    (C₁ C₂ : ℝ) :
    ∃ B : ℝ, ∀ (u : M → ℝ) (e c : ℝ),
      AEMeasurable u μ → Integrable (fun x => (u x)^2) μ →
      (∫ x in V, (u x - c)^2 ∂μ) ≤ C₁ * e →
      (∫ x in W, (u x)^2 ∂μ) ≤ C₂ * e →
      (∫ x in V, (u x)^2 ∂μ) ≤ B * e := by
  let O := V ∩ W
  have hOm : MeasurableSet O := (hV.inter hW).measurableSet
  have hm : 0 < μ.real O :=
    ENNReal.toReal_pos ((hV.inter hW).measure_pos μ hO).ne' (measure_ne_top μ O)
  let D := 2 * (C₁ + C₂) / μ.real O
  refine ⟨2 * (C₁ + μ.real V * D),fun u e c hu hu₂ hc hwu => ?_⟩
  have hp := integrable_sq_sub_const hu hu₂ c
  have h₁ : (∫ x in O, (u x - c)^2 ∂μ) ≤ C₁ * e :=
    (setIntegral_mono_set hp.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall inter_subset_left)).trans hc
  have h₂ : (∫ x in O, (u x)^2 ∂μ) ≤ C₂ * e :=
    (setIntegral_mono_set hu₂.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall inter_subset_right)).trans hwu
  have hC : c^2 ≤ D * e := by
    have ha := integral_sq_le_twice hOm (a := u) (b := fun x => -(u x - c))
      hu₂.integrableOn (by simpa only [neg_sq] using hp.integrableOn (s := O))
      (f := fun _ => c) (by intro x _; change c = u x + -(u x - c); ring)
    simp only [setIntegral_const,smul_eq_mul,neg_sq] at ha
    have hh : c^2 * μ.real O ≤ 2 * (C₁ + C₂) * e := by linarith
    exact ((le_div_iff₀ hm).mpr hh).trans_eq (by unfold D; ring)
  have h := integral_sq_le_twice hV.measurableSet (a := fun x => u x - c) (b := fun _ => c)
    hp.integrableOn (integrable_const _ : IntegrableOn (fun _ => c^2) V μ)
    (f := u) (by intro x _; change u x = u x - c + c; ring)
  simp only [setIntegral_const,smul_eq_mul] at h
  calc
    _ ≤ 2 * ((∫ x in V, (u x - c)^2 ∂μ) + μ.real V * c^2) := h
    _ ≤ 2 * (C₁ * e + μ.real V * (D * e)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hc (mul_le_mul_of_nonneg_left hC measureReal_nonneg)) (by norm_num)
    _ = _ := by ring

variable [PreconnectedSpace M] [CompactSpace M] [μ.IsOpenPosMeasure]

/-- On a connected compact space whose measure is positive on
nonempty open sets, local squared estimates up to constants and one
anchored squared estimate imply a global absolute estimate. -/
theorem exists_integral_sq_le_of_local_poincare
    (P : (M → ℝ) → Prop) (E : (M → ℝ) → ℝ)
    (hInt : ∀ u, P u → AEMeasurable u μ ∧ Integrable (fun x => (u x)^2) μ)
    (hLocal : ∀ p : M, ∃ V : Set M, p ∈ V ∧ IsOpen V ∧ ∃ C : ℝ,
      ∀ u, P u → ∃ c : ℝ, (∫ x in V, (u x - c)^2 ∂μ) ≤ C * E u)
    {A : Set M} (hA : IsOpen A) (hnA : A.Nonempty) (C₀ : ℝ)
    (hAnchor : ∀ u, P u → (∫ x in A, (u x)^2 ∂μ) ≤ C₀ * E u) :
    ∃ C : ℝ, ∀ u, P u → (∫ x, (u x)^2 ∂μ) ≤ C * E u := by
  classical
  let Good (V : Set M) := ∃ C : ℝ, ∀ u, P u → (∫ x in V, (u x)^2 ∂μ) ≤ C * E u
  let S := {V : Set M // IsOpen V ∧ Good V}
  let U := ⋃ V : S, (V : Set M)
  have hU : IsOpen U := isOpen_iUnion (fun V : S => V.2.1)
  have hAU : A ⊆ U := fun x hx => mem_iUnion.mpr ⟨⟨A,hA,⟨C₀,hAnchor⟩⟩,hx⟩
  have hCompl : IsOpen Uᶜ := by
    refine isOpen_iff_forall_mem_open.mpr ?_
    intro p hp
    obtain ⟨V,hpV,hV,C,hC⟩ := hLocal p
    refine ⟨V,?_,hV,hpV⟩
    intro q hqV hqU
    obtain ⟨W,hqW⟩ := mem_iUnion.mp hqU
    obtain ⟨C',hC'⟩ := W.2.2
    obtain ⟨B,hB⟩ := integral_sq_le_of_open_overlap (μ := μ) hV W.2.1 ⟨q,hqV,hqW⟩ C C'
    have hGood : Good V := by
      refine ⟨B,fun u hu => ?_⟩
      obtain ⟨c,hc⟩ := hC u hu
      exact hB u (E u) c (hInt u hu).1 (hInt u hu).2 hc (hC' u hu)
    exact hp (mem_iUnion.mpr ⟨⟨V,hV,hGood⟩,hpV⟩)
  have hAll : U = univ := IsClopen.eq_univ ⟨by simpa only [compl_compl] using hCompl.isClosed_compl, hU⟩ (hnA.mono hAU)
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun V : S => (V : Set M))
    (fun V => V.2.1) (le_of_eq hAll.symm)
  choose C hC using (fun V : S => V.2.2)
  refine ⟨∑ V ∈ s, C V,fun u hu => ?_⟩
  let f (x : M) := (u x)^2
  let fLocal (V : S) := (V : Set M).indicator f
  have hf : Integrable f μ := (hInt u hu).2
  have hI (V : S) : Integrable (fLocal V) μ := hf.indicator V.2.1.measurableSet
  have hCover (x : M) : f x ≤ ∑ V ∈ s, fLocal V x := by
    obtain ⟨V,hVs,hxV⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    have hx : fLocal V x = f x := indicator_of_mem hxV _
    rw [← hx]
    exact Finset.single_le_sum (fun W _ => indicator_nonneg (fun _ _ => sq_nonneg _) _) hVs
  calc
    _ ≤ ∫ x, ∑ V ∈ s, fLocal V x ∂μ :=
      integral_mono hf (integrable_finsetSum _ (fun V _ => hI V)) hCover
    _ = ∑ V ∈ s, ∫ x in (V : Set M), f x ∂μ := by
      rw [integral_finsetSum _ (fun V _ => hI V)]
      exact Finset.sum_congr rfl (fun V _ => integral_indicator V.2.1.measurableSet)
    _ ≤ ∑ V ∈ s, C V * E u := Finset.sum_le_sum (fun V _ => hC V u hu)
    _ = _ := (Finset.sum_mul ..).symm

end CalderonPatch
