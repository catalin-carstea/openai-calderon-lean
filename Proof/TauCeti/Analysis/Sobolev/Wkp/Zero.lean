/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.W1p.Zero
public import Proof.TauCeti.Analysis.Sobolev.Wkp.Basic

 





































public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Omega : Opens E}

 

section TestFunctionIteratedGradient

variable [CompleteSpace E]

 

noncomputable def iteratedGradientTestFunction (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    E → IteratedGradient E k :=
  iteratedGradientChain (phi : E → ℝ) k

 


theorem iteratedGradientTestFunction_def (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    iteratedGradientTestFunction phi k = iteratedGradientChain (phi : E → ℝ) k :=
  (rfl)

@[simp]
theorem iteratedGradientTestFunction_zero (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunction phi 0 = fun x => gradient (phi : E → ℝ) x :=
  by rw [iteratedGradientTestFunction, iteratedGradientChain_zero]

@[simp]
theorem iteratedGradientTestFunction_succ (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    iteratedGradientTestFunction phi (k + 1) =
      fderiv ℝ (iteratedGradientTestFunction phi k) :=
  by simp only [iteratedGradientTestFunction, iteratedGradientChain_succ]

 
theorem contDiff_iteratedGradientTestFunction (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedGradientTestFunction phi k) :=
  contDiff_iff_contDiffAt.mpr fun _ =>
    contDiffAt_iteratedGradientChain phi.contDiff.contDiffAt k (by simp)

 
theorem hasCompactSupport_iteratedGradientTestFunction (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    HasCompactSupport (iteratedGradientTestFunction phi k) :=
  hasCompactSupport_iteratedGradientChain phi.hasCompactSupport k

variable [MeasurableSpace E] [OpensMeasurableSpace E] {mu : Measure E}
  [IsFiniteMeasureOnCompacts mu]

 
theorem memLp_iteratedGradientTestFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    MemLp (iteratedGradientTestFunction phi k) q (mu.restrict Omega) :=
  (contDiff_iteratedGradientTestFunction phi k).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_iteratedGradientTestFunction phi k)

 

noncomputable def iteratedGradientTestFunctionLp (q : ENNReal) (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) : Lp (IteratedGradient E k) q (mu.restrict Omega) :=
  (memLp_iteratedGradientTestFunction (mu := mu) q phi k).toLp _

@[simp]
theorem iteratedGradientTestFunctionLp_apply_ae (q : ENNReal) (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega,
      iteratedGradientTestFunctionLp (mu := mu) q k phi x =
        iteratedGradientTestFunction phi k x :=
  (memLp_iteratedGradientTestFunction (mu := mu) q phi k).coeFn_toLp

 
@[simp]
theorem iteratedGradientTestFunctionLp_zero (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) q 0 phi = gradientTestFunctionLp q phi :=
  by
    apply Lp.ext
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q phi,
      iteratedGradientTestFunctionLp_apply_ae (mu := mu) q 0 phi] with x hx hy
    exact hy.trans ((congrFun (iteratedGradientTestFunction_zero phi) x).trans hx.symm)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedGradientTestFunction_add (k : ℕ) (phi psi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunction (phi + psi) k =
      iteratedGradientTestFunction phi k + iteratedGradientTestFunction psi k := by
  induction k with
  | zero =>
      funext x
      simp only [Pi.add_apply]
      rw [congrFun (iteratedGradientTestFunction_zero (phi + psi)) x,
        congrFun (iteratedGradientTestFunction_zero phi) x,
        congrFun (iteratedGradientTestFunction_zero psi) x]
      simpa using gradient_add ((phi.contDiff.differentiable (by simp)) x)
        ((psi.contDiff.differentiable (by simp)) x)
  | succ k ih =>
      rw [iteratedGradientTestFunction_succ, iteratedGradientTestFunction_succ,
        iteratedGradientTestFunction_succ, ih]
      funext x
      exact fderiv_add
        ((contDiff_iteratedGradientTestFunction phi k).differentiable (by simp) x)
        ((contDiff_iteratedGradientTestFunction psi k).differentiable (by simp) x)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedGradientTestFunction_smul (k : ℕ) (c : ℝ)
    (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunction (c • phi) k =
      c • iteratedGradientTestFunction phi k := by
  induction k with
  | zero =>
      funext x
      simp only [Pi.smul_apply]
      rw [congrFun (iteratedGradientTestFunction_zero (c • phi)) x,
        congrFun (iteratedGradientTestFunction_zero phi) x]
      simpa using gradient_const_smul (f := (phi : E → ℝ)) (x := x) c
  | succ k ih =>
      rw [iteratedGradientTestFunction_succ, iteratedGradientTestFunction_succ, ih]
      funext x
      exact fderiv_const_smul
        ((contDiff_iteratedGradientTestFunction phi k).differentiable (by simp) x) c

@[simp]
theorem iteratedGradientTestFunctionLp_add (q : ENNReal) (k : ℕ)
    (phi psi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) q k (phi + psi) =
      iteratedGradientTestFunctionLp (mu := mu) q k phi +
        iteratedGradientTestFunctionLp (mu := mu) q k psi := by
  rw [iteratedGradientTestFunctionLp, iteratedGradientTestFunctionLp,
    iteratedGradientTestFunctionLp, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (iteratedGradientTestFunction_add k phi psi) x

@[simp]
theorem iteratedGradientTestFunctionLp_smul (q : ENNReal) (k : ℕ) (c : ℝ)
    (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) q k (c • phi) =
      c • iteratedGradientTestFunctionLp (mu := mu) q k phi := by
  rw [iteratedGradientTestFunctionLp, iteratedGradientTestFunctionLp,
    ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (iteratedGradientTestFunction_smul k c phi) x

end TestFunctionIteratedGradient

section WkpZero

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
 

theorem hasWeakFDerivOn_iteratedGradientTestFunctionLp (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (iteratedGradientTestFunctionLp (mu := mu) p k phi)
      (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi) := by
  have hsmooth := contDiff_iteratedGradientTestFunction phi k
  have hclassical : HasWeakFDerivOn mu Omega (iteratedGradientTestFunction phi k)
      (fderiv ℝ (iteratedGradientTestFunction phi k)) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hsmooth.continuous.locallyIntegrable (μ := mu)).locallyIntegrableOn (Omega : Set E))
      (((contDiff_infty_iff_fderiv.mp hsmooth).2.continuous.locallyIntegrable
        (μ := mu)).locallyIntegrableOn (Omega : Set E))
      fun x _ => (hsmooth.differentiable (by simp)) x
  refine (hclassical.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) p k phi]
      with x hx using hx.symm
  · filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) p (k + 1) phi]
      with x hx
    simpa only [iteratedGradientTestFunction_succ] using hx.symm

 

private structure TestFunctionWkpPackage (phi : 𝓓(Omega, ℝ)) (k : ℕ) where
  element : Wkp mu Omega p (k + 1)
  value_eq : Wkp.value (k + 1) element = testFunctionLp p phi
  iteratedGradient_eq : Wkp.iteratedGradient k element =
    iteratedGradientTestFunctionLp (mu := mu) p k phi

private noncomputable def testFunctionWkpPackage (phi : 𝓓(Omega, ℝ)) :
    (k : ℕ) → TestFunctionWkpPackage (mu := mu) (p := p) phi k
  | 0 =>
       
      { element := W1p.ofTestFunctionₗ mu Omega p phi
        value_eq := by
          exact (Wkp.value_one (W1p.ofTestFunctionₗ mu Omega p phi)).trans
            (W1p.value_ofTestFunctionₗ (mu := mu) (p := p) phi)
        iteratedGradient_eq := by
          rw [Wkp.iteratedGradient_zero (W1p.ofTestFunctionₗ mu Omega p phi),
            W1p.gradient_ofTestFunctionₗ, iteratedGradientTestFunctionLp_zero] }
  | k + 1 =>
      let previous := testFunctionWkpPackage phi k
      let hweak : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient k previous.element)
          (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi) := by
        rw [previous.iteratedGradient_eq]
        exact hasWeakFDerivOn_iteratedGradientTestFunctionLp k phi
      { element := Wkp.mk k previous.element
          (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi) hweak
        value_eq := by
          rw [Wkp.value_mk]
          exact previous.value_eq
        iteratedGradient_eq := Wkp.iteratedGradient_mk k previous.element _ hweak }

private noncomputable def Wkp.ofTestFunction (k : ℕ) (phi : 𝓓(Omega, ℝ)) : Wkp mu Omega p k :=
  match k with
  | 0 => testFunctionLp p phi
  | k + 1 => (testFunctionWkpPackage (mu := mu) (p := p) phi k).element

private theorem Wkp.value_ofTestFunction (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.value k (Wkp.ofTestFunction (mu := mu) (p := p) k phi) = testFunctionLp p phi := by
  cases k with
  | zero => simp [Wkp.ofTestFunction]
  | succ k => exact (testFunctionWkpPackage (mu := mu) (p := p) phi k).value_eq

 
noncomputable def Wkp.ofTestFunctionₗ (k : ℕ) : 𝓓(Omega, ℝ) →ₗ[ℝ] Wkp mu Omega p k where
  toFun := Wkp.ofTestFunction (mu := mu) (p := p) k
  map_add' phi psi := by
    apply Wkp.ext k
    simp only [← Wkp.valueL_apply, map_add]
    simp only [Wkp.valueL_apply, Wkp.value_ofTestFunction, testFunctionLp_add]
  map_smul' c phi := by
    apply Wkp.ext k
    simp only [RingHom.id_apply, ← Wkp.valueL_apply, map_smul]
    simp only [Wkp.valueL_apply, Wkp.value_ofTestFunction, testFunctionLp_smul]

private theorem Wkp.ofTestFunctionₗ_apply (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi = Wkp.ofTestFunction k phi :=
  rfl

 
@[simp]
theorem Wkp.value_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.value k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi) = testFunctionLp p phi := by
  rw [Wkp.ofTestFunctionₗ_apply]
  exact Wkp.value_ofTestFunction k phi

 

theorem Wkp.iteratedGradient_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.iteratedGradient k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 1) phi) =
      iteratedGradientTestFunctionLp (mu := mu) p k phi :=
  (testFunctionWkpPackage (mu := mu) (p := p) phi k).iteratedGradient_eq

 


theorem Wkp.lowerOrder_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.lowerOrder k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 1) phi) =
      Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi := by
  apply Wkp.ext k
  rw [← Wkp.value_succ, Wkp.value_ofTestFunctionₗ, Wkp.value_ofTestFunctionₗ]

 
theorem Wkp.ofTestFunctionₗ_injective (k : ℕ) :
    Function.Injective (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k) := by
  intro phi psi h
  apply testFunctionLp_injective (nu := mu) (U := Omega) p
  simpa only [Wkp.value_ofTestFunctionₗ] using congrArg (Wkp.value k) h

 

@[simp]
theorem Wkp.ofTestFunctionₗ_one :
    Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) 1 =
      W1p.ofTestFunctionₗ mu Omega p := by
   
  apply LinearMap.ext
  intro phi
  apply W1p.ext_value
  have hvalue : W1p.value (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1 phi) =
      testFunctionLp p phi := by
    simpa only [Wkp.value_one] using
      Wkp.value_ofTestFunctionₗ (mu := mu) (p := p) 1 phi
  exact hvalue.trans (W1p.value_ofTestFunctionₗ (mu := mu) (p := p) phi).symm

 

 

noncomputable def wkp0Submodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 ≤ p)] (k : ℕ) : ClosedSubmodule ℝ (Wkp mu Omega p k) :=
  (LinearMap.range (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k)).closure

 
theorem coe_wkp0Submodule (k : ℕ) :
    (wkp0Submodule mu Omega p k : Set (Wkp mu Omega p k)) =
      closure (Set.range (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k)) := by
  rw [wkp0Submodule, Submodule.coe_closure, LinearMap.coe_range]

 
theorem Wkp.ofTestFunctionₗ_mem_wkp0Submodule (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi ∈ wkp0Submodule mu Omega p k :=
  Submodule.mem_closure_iff.2 (Submodule.le_topologicalClosure _ ⟨phi, rfl⟩)

 
theorem wkp0Submodule_subset_of_isClosed (k : ℕ) {s : Set (Wkp mu Omega p k)}
    (hs : IsClosed s) (h : ∀ phi, Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi ∈ s) :
    (wkp0Submodule mu Omega p k : Set (Wkp mu Omega p k)) ⊆ s := by
  rw [coe_wkp0Submodule]
  exact closure_minimal (by rintro _ ⟨phi, rfl⟩; exact h phi) hs

 

@[simp]
theorem wkp0Submodule_one : wkp0Submodule mu Omega p 1 = w1p0Submodule mu Omega p := by
   
  apply SetLike.coe_injective
  rw [coe_wkp0Submodule, Wkp.ofTestFunctionₗ_one]
  exact (coe_w1p0Submodule (mu := mu) (Omega := Omega) (p := p)).symm

 
noncomputable abbrev Wkp0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 ≤ p)] (k : ℕ) := (wkp0Submodule mu Omega p k).toSubmodule

 
def Wkp0.ofTestFunctionₗ (k : ℕ) : 𝓓(Omega, ℝ) →ₗ[ℝ] Wkp0 mu Omega p k :=
  (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k).codRestrict
    (wkp0Submodule mu Omega p k).toSubmodule (Wkp.ofTestFunctionₗ_mem_wkp0Submodule k)

 
@[simp]
theorem Wkp0.coe_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    (Wkp0.ofTestFunctionₗ (mu := mu) (p := p) k phi : Wkp mu Omega p k) =
      Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi :=
  (rfl)

 
theorem Wkp0.denseRange_ofTestFunctionₗ (k : ℕ) :
    DenseRange (Wkp0.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k) := by
  intro u
  rw [closure_subtype, ← Set.range_comp]
  have hu : (u : Wkp mu Omega p k) ∈
      (wkp0Submodule mu Omega p k : Set (Wkp mu Omega p k)) := u.2
  rw [coe_wkp0Submodule] at hu
  simpa only [Function.comp_def, Wkp0.coe_ofTestFunctionₗ] using hu

 
theorem Wkp.lowerOrder_mem_wkp0Submodule (k : ℕ) {u : Wkp mu Omega p (k + 1)}
    (hu : u ∈ wkp0Submodule mu Omega p (k + 1)) :
    Wkp.lowerOrder k u ∈ wkp0Submodule mu Omega p k := by
  rw [← Wkp.lowerOrderL_apply]
  refine wkp0Submodule_subset_of_isClosed (k + 1)
    ((wkp0Submodule mu Omega p k).isClosed.preimage (Wkp.lowerOrderL k).continuous)
    (fun phi => ?_) hu
  rw [Set.mem_preimage, Wkp.lowerOrderL_apply k, Wkp.lowerOrder_ofTestFunctionₗ k]
  exact Wkp.ofTestFunctionₗ_mem_wkp0Submodule k phi

 
def Wkp0.lowerOrderL (k : ℕ) : Wkp0 mu Omega p (k + 1) →L[ℝ] Wkp0 mu Omega p k :=
  ((Wkp.lowerOrderL k).comp (wkp0Submodule mu Omega p (k + 1)).toSubmodule.subtypeL).codRestrict
    (wkp0Submodule mu Omega p k).toSubmodule
    (fun u => by
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Wkp.lowerOrderL_apply k]
      exact Wkp.lowerOrder_mem_wkp0Submodule k u.2)

 
 
theorem Wkp0.coe_lowerOrderL (k : ℕ) (u : Wkp0 mu Omega p (k + 1)) :
    (Wkp0.lowerOrderL k u : Wkp mu Omega p k) =
      Wkp.lowerOrder k (u : Wkp mu Omega p (k + 1)) :=
  Wkp.lowerOrderL_apply k (u : Wkp mu Omega p (k + 1))

 

 
theorem Wkp0.lowerOrderL_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp0.lowerOrderL k (Wkp0.ofTestFunctionₗ (mu := mu) (p := p) (k + 1) phi) =
      Wkp0.ofTestFunctionₗ (mu := mu) (p := p) k phi := by
  apply Subtype.ext
  rw [Wkp0.coe_lowerOrderL, Wkp0.coe_ofTestFunctionₗ, Wkp0.coe_ofTestFunctionₗ,
    Wkp.lowerOrder_ofTestFunctionₗ]

 
instance (k : ℕ) : CompleteSpace (Wkp0 mu Omega p k) :=
  (wkp0Submodule mu Omega p k).isClosed.completeSpace_coe

end WkpZero

end TauCeti
