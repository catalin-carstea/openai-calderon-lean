module

public import Proof.CalderonPatch.HalfSpaceZeroSupport
public import Proof.CalderonN.WeakPartialEquation

import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Extension
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace TauCeti
open scoped ENNReal InnerProductSpace

namespace CalderonPatch

open CalderonN (X I)
open CalderonN.WeakTest (e coordDeriv symmDeriv gradient_d1_coordinate coord_eq_inner)
open CalderonN.WkpCalculus (d0 d1 value_d1)

variable {n : ℕ} [NeZero n]
local notation "E" => X n
local notation "H" => positiveHalfSpaceOpens n
local notation "μ" => (volume : Measure E)

private theorem memLp_indicator_top_of_lp {F : Type*} [NormedAddCommGroup F]
    (u : Lp F 2 ((μ).restrict H)) :
    MemLp ((H : Set E).indicator (u : E → F)) 2 ((μ).restrict (⊤ : Opens E)) := by
  simpa only [Opens.coe_top,Measure.restrict_univ] using
    (memLp_indicator_iff_restrict (H).isOpen.measurableSet.nullMeasurableSet).2 (Lp.memLp u)

omit [NeZero n] in
private theorem ae_indicator_apply {F G : Type*} [Zero F] [Zero G]
    {V : Set E} (hV : MeasurableSet V) {u : E → F} {g : E → G} (P : F → G)
    (hP : P 0 = 0) (h : (fun x => P (u x)) =ᵐ[(μ).restrict V] g) :
    (fun x => P (V.indicator u x)) =ᵐ[μ] V.indicator g := by
  filter_upwards [(ae_restrict_iff' hV).1 h] with x hx
  by_cases hxV : x ∈ V
  · simpa only [indicator_of_mem hxV] using hx hxV
  · rw [indicator_of_notMem hxV,indicator_of_notMem hxV,hP]

/-- A tangential derivative of an H² function with zero Dirichlet
trace belongs to the same zero-trace H¹ space. -/
theorem wkp_two_tangential_derivative_mem_w1p0
    (V : Wkp μ H 2 2) (hV : Wkp.lowerOrder 1 V ∈ w1p0Submodule μ H 2)
    (j : I n) (hj : j ≠ 0) : d1 j V ∈ w1p0Submodule μ H 2 := by
  let u := Wkp.lowerOrder 1 V
  let G := (W1p.gradient u : E → E)
  let d := d1 j V
  let A := (W1p.gradient d : E → E)
  let G₀ := (H : Set E).indicator G
  let A₀ := (H : Set E).indicator A
  let u₀ := (H : Set E).indicator (W1p.value u : E → ℝ)
  let d₀ := (H : Set E).indicator (W1p.value d : E → ℝ)
  have hface : MeasurableSet (H : Set E) := (H).isOpen.measurableSet
  have hU : HasWeakFDerivOn μ ⊤ u₀ (fun x => innerSL ℝ (G₀ x)) :=
    W1p0.hasWeakFDerivOn_indicator (le_top : H ≤ ⊤) ⟨u,hV⟩
  have hD : HasWeakFDerivOn μ H G (Wkp.iteratedGradient 1 V : E → E →L[ℝ] E) := by
    simpa only [G,u,Wkp.iteratedGradient_zero] using Wkp.hasWeakFDerivOn_iteratedGradient 0 V
  have hgj : (fun x => G x j) =ᵐ[(μ).restrict H] W1p.value d := by
    rw [show W1p.value d = d0 j u from value_d1 j V]
    exact EventuallyEq.symm (ContinuousLinearMap.coeFn_compLp (EuclideanSpace.proj j : E →L[ℝ] ℝ)
      (Wkp.iteratedGradient 0 u))
  have hjval : (fun x => G₀ x j) =ᵐ[(μ).restrict (⊤ : Opens E)] d₀ := by
    simpa only [d₀,G₀,Opens.coe_top,Measure.restrict_univ] using
      ae_indicator_apply hface (fun y : E => y j) rfl hgj
  have hfirst := fun i => coordDeriv hU i
  have hA : MemLp A₀ 2 ((μ).restrict (⊤ : Opens E)) := memLp_indicator_top_of_lp (W1p.gradient d)
  have hG : MemLp G₀ 2 ((μ).restrict (⊤ : Opens E)) := memLp_indicator_top_of_lp (W1p.gradient u)
  have hd : MemLp d₀ 2 ((μ).restrict (⊤ : Opens E)) := memLp_indicator_top_of_lp (W1p.value d)
  have hcoord (i : I n) : HasWeakLineDerivOn μ ⊤ d₀ (fun x => A₀ x i) (e i) := by
    have hLoc : HasWeakLineDerivOn μ H (fun x => G x i) (fun x => A x i) (e j) :=
      (symmDeriv (W1p.hasWeakFDerivOn u) hD i j).congr_ae_deriv
        (gradient_d1_coordinate V j i).symm
    have hLoc₀ : HasWeakLineDerivOn μ H (fun x => G₀ x i) (fun x => A₀ x i) (e j) := by
      refine (hLoc.congr_ae ?_).congr_ae_deriv ?_
      · filter_upwards [ae_restrict_mem hface] with x hx
        change G x i = (H : Set E).indicator G x i
        rw [indicator_of_mem hx]
      · filter_upwards [ae_restrict_mem hface] with x hx
        change A x i = (H : Set E).indicator A x i
        rw [indicator_of_mem hx]
    have hG' : MemLp (fun x => G₀ x i) 2 μ := by
      have hWhole : MemLp G₀ 2 μ := by
        simpa only [Opens.coe_top,Measure.restrict_univ] using hG
      change MemLp ((EuclideanSpace.proj i : E →L[ℝ] ℝ) ∘ G₀) 2 μ
      exact (EuclideanSpace.proj i : E →L[ℝ] ℝ).comp_memLp' hWhole
    have hA' : MemLp (fun x => A₀ x i) 2 μ := by
      have hWhole : MemLp A₀ 2 μ := by
        simpa only [Opens.coe_top,Measure.restrict_univ] using hA
      change MemLp ((EuclideanSpace.proj i : E →L[ℝ] ℝ) ∘ A₀) 2 μ
      exact (EuclideanSpace.proj i : E →L[ℝ] ℝ).comp_memLp' hWhole
    have htan : (e j : E) 0 = 0 := by simp [e, Ne.symm hj]
    have hExt := hasWeakLineDerivOn_top_of_positiveHalfSpace hLoc₀ htan
      (hG'.locallyIntegrable (by norm_num)) (hA'.locallyIntegrable (by norm_num))
      (fun x hx => by change (H : Set E).indicator G x i = 0; rw [indicator_of_notMem (show x ∉ (H : Set E) from hx)]; rfl)
      (fun x hx => by change (H : Set E).indicator A x i = 0; rw [indicator_of_notMem (show x ∉ (H : Set E) from hx)]; rfl)
    exact ((hfirst i).comm hExt (hfirst j)).congr_ae hjval
  have hDiff : HasWeakFDerivOn μ ⊤ d₀ (fun x => innerSL ℝ (A₀ x)) := by
    apply (EuclideanSpace.basisFun (I n) ℝ).toBasis.hasWeakFDerivOn_of_forall
      (hfirst j |>.congr_ae_deriv hjval |>.locallyIntegrableOn_deriv)
    intro i
    rw [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply]
    change HasWeakLineDerivOn μ ⊤ d₀ (fun x => ⟪A₀ x, e i⟫_ℝ) (e i)
    simpa only [← coord_eq_inner] using hcoord i
  let w : W1p μ ⊤ 2 := W1p.mk (hd.toLp d₀) (hA.toLp A₀)
    ((hDiff.congr_ae hd.coeFn_toLp.symm).congr_ae_deriv (by
      filter_upwards [hA.coeFn_toLp] with x hx
      rw [hx]))
  have hwval : (W1p.value w : E → ℝ) =ᵐ[μ] d₀ := by
    simpa only [w,W1p.value_mk,Opens.coe_top,Measure.restrict_univ] using hd.coeFn_toLp
  have hw0 : ∀ᵐ x ∂μ, x ∉ positiveHalfSpace n → W1p.value w x = 0 := by
    filter_upwards [hwval] with x hx hxH
    rw [hx,show d₀ x = 0 from indicator_of_notMem (show x ∉ (H : Set E) from hxH) _]
  have hmem := restrictL_mem_w1p0_of_zero_off_positiveHalfSpace w hw0
  have hEq : W1p.restrictL (U := H) le_top w = d := by
    apply W1p.ext_value
    apply Lp.ext
    filter_upwards [W1p.value_restrictL_ae (U := H) le_top w,ae_restrict_of_ae hwval,
      ae_restrict_mem hface] with x hr hs hx
    rw [hr,hs,show d₀ x = W1p.value d x from indicator_of_mem hx _]
  rwa [hEq] at hmem

end CalderonPatch
