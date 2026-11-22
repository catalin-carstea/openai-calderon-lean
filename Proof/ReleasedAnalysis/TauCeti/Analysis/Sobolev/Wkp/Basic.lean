/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.IteratedGradient
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.GraphStep
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Basic

/-! From Proof/TauCeti/Analysis/Sobolev/Wkp/Basic.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 




























































public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace

universe u

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

 

structure SobolevStage (mu : Measure E) (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] (j : ℕ) where
   
  Space : Type u
   
  [normedAddCommGroup : NormedAddCommGroup Space]
   
  [normedSpace : NormedSpace ℝ Space]
   
  [completeSpace : CompleteSpace Space]
   
  iteratedGradientL : Space →L[ℝ] Lp (IteratedGradient E j) p (mu.restrict Omega)

 

@[reducible, expose] def firstSobolevStage : SobolevStage mu Omega p 0 where
  Space := W1p mu Omega p
  iteratedGradientL := W1p.gradientL

 
@[reducible, expose] def SobolevStage.next {j : ℕ} (S : SobolevStage mu Omega p j) :
    SobolevStage mu Omega p (j + 1) :=
  letI : NormedAddCommGroup S.Space := S.normedAddCommGroup
  letI : NormedSpace ℝ S.Space := S.normedSpace
  letI : CompleteSpace S.Space := S.completeSpace
  { Space := WeakDerivStep mu Omega p S.iteratedGradientL
    iteratedGradientL := WeakDerivStep.weakFDerivL S.iteratedGradientL }

 
@[expose] def sobolevStage : (j : ℕ) → SobolevStage mu Omega p j
  | 0 => firstSobolevStage
  | j + 1 => (sobolevStage j).next

@[instance_reducible, expose] def SobolevStage.instNormedAddCommGroup
    (j : ℕ) : NormedAddCommGroup
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).normedAddCommGroup

attribute [instance] SobolevStage.instNormedAddCommGroup

@[instance_reducible, expose] def SobolevStage.instNormedSpace
    (j : ℕ) : NormedSpace ℝ
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).normedSpace

attribute [instance] SobolevStage.instNormedSpace

theorem SobolevStage.instCompleteSpace (j : ℕ) :
    CompleteSpace (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).completeSpace

attribute [instance] SobolevStage.instCompleteSpace

 


@[reducible, expose] def Wkp (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] : ℕ → Type u
  | 0 => Lp ℝ p (mu.restrict Omega)
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).Space

@[instance_reducible, expose] def Wkp.instNormedAddCommGroup :
    (k : ℕ) → NormedAddCommGroup (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).normedAddCommGroup

attribute [instance] Wkp.instNormedAddCommGroup

@[instance_reducible, expose] def Wkp.instNormedSpace :
    (k : ℕ) → NormedSpace ℝ (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).normedSpace

attribute [instance] Wkp.instNormedSpace

 
theorem Wkp.instCompleteSpace :
    (k : ℕ) → CompleteSpace (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).completeSpace

attribute [instance] Wkp.instCompleteSpace

namespace Wkp

 
@[expose] def lowerOrderL : (k : ℕ) → Wkp mu Omega p (k + 1) →L[ℝ] Wkp mu Omega p k
  | 0 => W1p.valueL
  | k + 1 => WeakDerivStep.prevL
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL

 
@[expose] def lowerOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) : Wkp mu Omega p k :=
  lowerOrderL k u

 
theorem lowerOrderL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    lowerOrderL k u = lowerOrder k u :=
  (rfl)

 
@[expose] def firstOrderL : (k : ℕ) → Wkp mu Omega p (k + 1) →L[ℝ] W1p mu Omega p
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (firstOrderL k).comp (lowerOrderL (k + 1))

 
@[expose] def firstOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) : W1p mu Omega p :=
  firstOrderL k u

 
theorem firstOrderL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    firstOrderL k u = firstOrder k u :=
  (rfl)

 
@[simp] theorem firstOrder_zero (u : Wkp mu Omega p 1) : firstOrder 0 u = u :=
   
   
  (rfl)

 
theorem firstOrder_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    firstOrder (k + 1) u = firstOrder k (lowerOrder (k + 1) u) :=
  (rfl)

 

@[expose] def iteratedGradientL (k : ℕ) : Wkp mu Omega p (k + 1) →L[ℝ]
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL

 
@[expose] def iteratedGradient (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  iteratedGradientL k u

 
theorem iteratedGradientL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    iteratedGradientL k u = iteratedGradient k u :=
  (rfl)

 
@[expose] def valueL : (k : ℕ) → Wkp mu Omega p k →L[ℝ] Lp ℝ p (mu.restrict Omega)
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (valueL k).comp (lowerOrderL k)

 
@[expose] def value (k : ℕ) (u : Wkp mu Omega p k) : Lp ℝ p (mu.restrict Omega) :=
  valueL k u

 
@[simp]
theorem valueL_apply (k : ℕ) (u : Wkp mu Omega p k) : valueL k u = value k u :=
  (rfl)

 
@[simp]
theorem value_add (k : ℕ) (u v : Wkp mu Omega p k) :
    value k (u + v) = value k u + value k v :=
  map_add (valueL k) u v

 
@[simp]
theorem value_smul (k : ℕ) (c : ℝ) (u : Wkp mu Omega p k) :
    value k (c • u) = c • value k u :=
  map_smul (valueL k) c u

 
@[simp]
theorem value_zero (u : Wkp mu Omega p 0) : value 0 u = u :=
  (rfl)

 
theorem value_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    value (k + 1) u = value k (lowerOrder k u) :=
  (rfl)

 
@[simp]
theorem lowerOrder_zero (u : Wkp mu Omega p 1) : lowerOrder 0 u = W1p.value u :=
   
   
   
  W1p.valueL_apply u

 
@[simp]
theorem value_one (u : Wkp mu Omega p 1) : value 1 u = W1p.value u := by
  simp only [value_succ, value_zero, lowerOrder_zero]

 
@[simp]
theorem iteratedGradient_zero (u : Wkp mu Omega p 1) :
    iteratedGradient 0 u = W1p.gradient u :=
   
   
   
  W1p.gradientL_apply u

 
@[simp] theorem value_firstOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    W1p.value (firstOrder k u) = value (k + 1) u := by
  induction k with
  | zero => exact (value_one u).symm
  | succ k ih => rw [firstOrder_succ, ih, value_succ (k + 1) u]

 
theorem iteratedGradient_eq_sobolevStage_iteratedGradientL
    (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    iteratedGradient k u =
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u :=
  (rfl)

 

theorem lowerOrder_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    lowerOrder (k + 1) u = WeakDerivStep.prev
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u :=
  WeakDerivStep.prevL_apply
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

 

theorem iteratedGradient_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    iteratedGradient (k + 1) u = WeakDerivStep.weakFDeriv
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u :=
  WeakDerivStep.weakFDerivL_apply
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

 

theorem hasWeakFDerivOn_value (u : Wkp mu Omega p 1) :
    HasWeakFDerivOn mu Omega (value 1 u)
      (fun x => innerSL ℝ (iteratedGradient 0 u x)) := by
  simpa only [value_one, iteratedGradient_zero] using
    W1p.hasWeakFDerivOn u

 

@[expose] def mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) : Wkp mu Omega p (k + 2) :=
  WeakDerivStep.mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u D h

 
@[simp]
theorem lowerOrder_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    lowerOrder (k + 1) (mk k u D h) = u := by
  rw [lowerOrder_succ]
  exact WeakDerivStep.prev_mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u D h

 
@[simp]
theorem value_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    value (k + 2) (mk k u D h) = value (k + 1) u := by
  rw [value_succ, lowerOrder_mk]

 
@[simp]
theorem iteratedGradient_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    iteratedGradient (k + 1) (mk k u D h) = D := by
  rw [iteratedGradient_succ]
  exact WeakDerivStep.weakFDeriv_mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u D h

 

theorem hasWeakFDerivOn_iteratedGradient (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    HasWeakFDerivOn mu Omega (iteratedGradient k (lowerOrder (k + 1) u))
      (iteratedGradient (k + 1) u) := by
  rw [iteratedGradient_eq_sobolevStage_iteratedGradientL, lowerOrder_succ,
    iteratedGradient_succ]
  exact WeakDerivStep.hasWeakFDerivOn_base_prev
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

 

theorem ext_lowerOrder (k : ℕ) {u v : Wkp mu Omega p (k + 1)}
    (h : lowerOrder k u = lowerOrder k v) : u = v := by
  cases k with
  | zero => exact W1p.ext_value (by simpa only [lowerOrder_zero] using h)
  | succ k =>
      rw [lowerOrder_succ, lowerOrder_succ] at h
      exact WeakDerivStep.ext h

 

@[ext]
theorem ext : ∀ (k : ℕ) {u v : Wkp mu Omega p k}, value k u = value k v → u = v
  | 0, _, _, h => by simpa only [value_zero] using h
  | k + 1, _, _, h => ext_lowerOrder k (ext k (by simpa only [value_succ] using h))

 
theorem norm_lowerOrder_le (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖lowerOrder k u‖ ≤ ‖u‖ := by
  cases k with
  | zero =>
      rw [lowerOrder_zero]
      exact W1p.norm_value_le u
  | succ k =>
      rw [lowerOrder_succ]
      exact WeakDerivStep.norm_prev_le
        (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

 
theorem norm_value_le : ∀ (k : ℕ) (u : Wkp mu Omega p k), ‖value k u‖ ≤ ‖u‖
  | 0, u => by simpa only [value_zero] using le_rfl
  | k + 1, u =>
      (norm_value_le k (lowerOrder k u)).trans (norm_lowerOrder_le k u)

 
theorem norm_iteratedGradient_le (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖iteratedGradient k u‖ ≤ ‖u‖ := by
  cases k with
  | zero =>
      rw [iteratedGradient_zero]
      exact W1p.norm_gradient_le u
  | succ k =>
      rw [iteratedGradient_succ]
      exact WeakDerivStep.norm_weakFDeriv_le
        (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

 

theorem norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) :
    ‖u‖ ^ 2 = ‖lowerOrder (k + 1) u‖ ^ 2 + ‖iteratedGradient (k + 1) u‖ ^ 2 := by
  rw [lowerOrder_succ, iteratedGradient_succ]
  exact WeakDerivStep.norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL u

 




theorem norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq (k : ℕ)
    (u : Wkp mu Omega 2 (k + 1)) :
    ‖u‖ ^ 2 = ‖lowerOrder k u‖ ^ 2 + ‖iteratedGradient k u‖ ^ 2 := by
  cases k with
  | zero =>
      rw [lowerOrder_zero, iteratedGradient_zero]
      exact W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  | succ k =>
      exact norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u

 

theorem tendsto_iff_lowerOrder_iteratedGradient (k : ℕ) {I : Type*} {l : Filter I}
    {v : I → Wkp mu Omega p (k + 1)} {u : Wkp mu Omega p (k + 1)} :
    Filter.Tendsto v l (nhds u) ↔
      Filter.Tendsto (fun i => lowerOrder k (v i)) l (nhds (lowerOrder k u)) ∧
      Filter.Tendsto (fun i => iteratedGradient k (v i)) l
        (nhds (iteratedGradient k u)) := by
  cases k with
  | zero =>
      simp only [lowerOrder_zero, iteratedGradient_zero]
      exact W1p.tendsto_iff_value_gradient
  | succ k =>
      simp only [lowerOrder_succ, iteratedGradient_succ]
      exact WeakDerivStep.tendsto_iff_prev_weakFDeriv
        (base := (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).iteratedGradientL)

 

theorem continuous_iff_lowerOrder_iteratedGradient (k : ℕ) {Y : Type*} [TopologicalSpace Y]
    {f : Y → Wkp mu Omega p (k + 1)} :
    Continuous f ↔
      Continuous (fun y => lowerOrder k (f y)) ∧
        Continuous (fun y => iteratedGradient k (f y)) := by
  simp only [continuous_iff_continuousAt]
  exact ⟨fun h => ⟨fun y => ((tendsto_iff_lowerOrder_iteratedGradient k).1 (h y)).1,
      fun y => ((tendsto_iff_lowerOrder_iteratedGradient k).1 (h y)).2⟩,
    fun h y => (tendsto_iff_lowerOrder_iteratedGradient k).2 ⟨h.1 y, h.2 y⟩⟩

end Wkp

end TauCeti
