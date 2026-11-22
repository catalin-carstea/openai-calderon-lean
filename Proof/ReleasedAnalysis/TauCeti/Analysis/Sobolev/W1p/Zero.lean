/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Basic

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! From Proof/TauCeti/Analysis/Sobolev/W1p/Zero.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 
















































public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

 

omit [Fact (1 ≤ p)] in
theorem hasWeakFDerivOn_testFunctionLp (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (testFunctionLp (mu := mu) p phi)
      fun x => innerSL ℝ (gradientTestFunctionLp (mu := mu) p phi x) := by
  refine ((hasWeakFDerivOn_testFunction (μ := mu) phi).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [testFunctionLp_apply_ae (mu := mu) p phi] with x hx using hx.symm
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) p phi] with x hx
    rw [hx]

 


@[expose] def W1p.ofTestFunctionₗ (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : 𝓓(Omega, ℝ) →ₗ[ℝ] W1p mu Omega p where
  toFun phi := W1p.mk (testFunctionLp p phi) (gradientTestFunctionLp p phi)
    (hasWeakFDerivOn_testFunctionLp phi)
  map_add' phi psi := by
    apply W1p.ext <;>
      simp only [← W1p.valueL_apply, ← W1p.gradientL_apply, map_add] <;> simp
  map_smul' c phi := by
    apply W1p.ext <;>
      simp only [← W1p.valueL_apply, ← W1p.gradientL_apply, map_smul] <;> simp

@[simp]
theorem W1p.value_ofTestFunctionₗ (phi : 𝓓(Omega, ℝ)) :
    W1p.value (W1p.ofTestFunctionₗ mu Omega p phi) = testFunctionLp p phi :=
  W1p.value_mk _ _ (hasWeakFDerivOn_testFunctionLp phi)

@[simp]
theorem W1p.gradient_ofTestFunctionₗ (phi : 𝓓(Omega, ℝ)) :
    W1p.gradient (W1p.ofTestFunctionₗ mu Omega p phi) = gradientTestFunctionLp p phi :=
  W1p.gradient_mk _ _ (hasWeakFDerivOn_testFunctionLp phi)

 



theorem W1p.ofTestFunctionₗ_injective :
    Function.Injective (W1p.ofTestFunctionₗ mu Omega p) := by
  intro phi psi h
  apply testFunctionLp_injective (nu := mu) (U := Omega) p
  simpa using congrArg W1p.value h

 

 


@[expose] def w1p0Submodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : ClosedSubmodule ℝ (W1p mu Omega p) :=
  (LinearMap.range (W1p.ofTestFunctionₗ mu Omega p)).closure

 
theorem coe_w1p0Submodule :
    (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) =
      closure (Set.range (W1p.ofTestFunctionₗ mu Omega p)) := by
  rw [w1p0Submodule, Submodule.coe_closure, LinearMap.coe_range]

 
theorem W1p.ofTestFunctionₗ_mem_w1p0Submodule (phi : 𝓓(Omega, ℝ)) :
    W1p.ofTestFunctionₗ mu Omega p phi ∈ w1p0Submodule mu Omega p :=
  Submodule.mem_closure_iff.2 (Submodule.le_topologicalClosure _ ⟨phi, rfl⟩)

 

theorem w1p0Submodule_subset_of_isClosed {s : Set (W1p mu Omega p)} (hs : IsClosed s)
    (h : ∀ phi, W1p.ofTestFunctionₗ mu Omega p phi ∈ s) :
    (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) ⊆ s := by
  rw [coe_w1p0Submodule]
  exact closure_minimal (by rintro _ ⟨phi, rfl⟩; exact h phi) hs

 
abbrev W1p0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] := (w1p0Submodule mu Omega p).toSubmodule

 

noncomputable instance instSeminormedAddCommGroupW1p0 :
    SeminormedAddCommGroup (W1p0 mu Omega p) := inferInstance

 

noncomputable instance instNormedSpaceW1p0 : NormedSpace ℝ (W1p0 mu Omega p) := inferInstance

 

@[expose] def W1p0.valueL : W1p0 mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  W1p.valueL.comp (w1p0Submodule mu Omega p).toSubmodule.subtypeL

@[simp]
theorem W1p0.valueL_apply (u : W1p0 mu Omega p) :
    W1p0.valueL u = W1p.value (u : W1p mu Omega p) :=
  by simp [W1p0.valueL]

 


theorem W1p0.denseRange_valueL_two :
    DenseRange (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) := by
  have hcoe : (LinearMap.range (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2) :
      W1p0 mu Omega 2 →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) :
        Set (Lp ℝ 2 (mu.restrict Omega))) =
      Set.range (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  have hdense : Dense ((LinearMap.range (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2) :
      W1p0 mu Omega 2 →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) :
        Set (Lp ℝ 2 (mu.restrict Omega)))) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro f hf
    apply Lp.ext
    have hzero : ∀ᵐ x ∂mu.restrict Omega, f x = 0 := by
      rw [ae_restrict_iff' Omega.isOpen.measurableSet]
      refine Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((Lp.memLp f).locallyIntegrable (by simp))) fun g hg hgc hgs => ?_
      let phi : 𝓓(Omega, ℝ) := ⟨g, hg, hgc, hgs⟩
      let u : W1p0 mu Omega 2 :=
        ⟨W1p.ofTestFunctionₗ mu Omega 2 phi, W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩
      have hinner : ⟪W1p0.valueL u, f⟫_ℝ = 0 := hf _ ⟨u, rfl⟩
      rw [L2.inner_def, W1p0.valueL_apply, W1p.value_ofTestFunctionₗ] at hinner
      calc
        ∫ x, g x • f x ∂mu = ∫ x in Omega, g x • f x ∂mu := by
          rw [← integral_indicator Omega.isOpen.measurableSet]
          congr 1
          symm
          apply Set.indicator_eq_self.2
          exact (Function.support_smul_subset_left g fun x => f x).trans
            ((subset_tsupport g).trans hgs)
        _ = 0 := by
          rw [← hinner]
          apply integral_congr_ae
          filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 phi] with x hx
          rw [hx]
          exact mul_comm _ _
    exact Filter.EventuallyEq.trans hzero
      (Lp.coeFn_zero ℝ 2 (mu.restrict Omega)).symm
  rw [hcoe] at hdense
  exact hdense

 
theorem W1p0.exists_value_ne_zero (hOmega : (Omega : Set E).Nonempty) :
    ∃ w : W1p0 mu Omega p, W1p.value (w : W1p mu Omega p) ≠ 0 := by
  obtain ⟨x, hx⟩ := hOmega
  obtain ⟨g, hgs, hgc, hg, _, hgx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (Omega.isOpen.mem_nhds hx)
  let phi : 𝓓(Omega, ℝ) := ⟨g, hg, hgc, hgs⟩
  let w : W1p0 mu Omega p :=
    ⟨W1p.ofTestFunctionₗ mu Omega p phi, W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩
  refine ⟨w, ?_⟩
  rw [W1p.value_ofTestFunctionₗ]
  intro hzero
  have hzeroTest : testFunctionLp (mu := mu) (Omega := Omega) p (0 : 𝓓(Omega, ℝ)) = 0 := by
    apply Lp.ext
    exact Filter.EventuallyEq.trans
      (testFunctionLp_apply_ae (mu := mu) p (0 : 𝓓(Omega, ℝ)))
      (Lp.coeFn_zero ℝ p (mu.restrict Omega)).symm
  have hphi : phi = 0 := testFunctionLp_injective p (hzero.trans hzeroTest.symm)
  have : g x = 0 := by
    have := congrArg (fun q : 𝓓(Omega, ℝ) => q x) hphi
    simpa [phi] using this
  linarith

 

theorem W1p0.valueL_ne_zero (hOmega : (Omega : Set E).Nonempty) :
    (W1p0.valueL (mu := mu) (Omega := Omega) (p := p)) ≠ 0 := by
  obtain ⟨w, hw⟩ := W1p0.exists_value_ne_zero (mu := mu) (Omega := Omega) (p := p) hOmega
  exact fun hzero => hw (by rw [← W1p0.valueL_apply, hzero, zero_apply])

 
instance : CompleteSpace (W1p0 mu Omega p) :=
  (w1p0Submodule mu Omega p).isClosed.completeSpace_coe

 




 



noncomputable local instance W1p0.instNormedAddCommGroup :
    NormedAddCommGroup (W1p0 mu Omega p) := inferInstance

 


noncomputable local instance W1p0.instInnerProductSpace :
    InnerProductSpace ℝ (W1p0 mu Omega 2) := inferInstance

end TauCeti
