/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

 
 
public import Mathlib.Analysis.Distribution.TestFunction
 
 
 
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
 
 
public import Mathlib.Analysis.Calculus.Gradient.Basic
 
 
public import Mathlib.LinearAlgebra.Basis.Defs

/-! From Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Basic.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 









































































































































public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {v : E}

 

 
theorem lineDeriv_eq_zero_of_notMem_tsupport (φ : 𝓓(Ω, ℝ)) {x : E}
    (hx : x ∉ tsupport (φ : E → ℝ)) (v : E) : lineDeriv ℝ (φ : E → ℝ) x v = 0 := by
  have hd : DifferentiableAt ℝ (φ : E → ℝ) x :=
    (φ.contDiff.differentiable (by simp)) x
  rw [hd.lineDeriv_eq_fderiv, fderiv_of_notMem_tsupport ℝ hx]
  simp

 

section Defs

variable [MeasurableSpace E] {μ : Measure E} {u u' : E → F}

 





















@[expose] def HasWeakLineDerivOn (μ : Measure E) (Ω : Opens E) (u u' : E → F) (v : E) : Prop :=
  CompleteSpace F ∧ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn u' Ω μ ∧
    ∀ φ : 𝓓(Ω, ℝ), ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ = -∫ x, (φ : E → ℝ) x • u' x ∂μ

 


theorem hasWeakLineDerivOn_iff_testFunction :
    HasWeakLineDerivOn μ Ω u u' v ↔
      CompleteSpace F ∧ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn u' Ω μ ∧
        ∀ φ : 𝓓(Ω, ℝ),
          ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ =
            -∫ x, (φ : E → ℝ) x • u' x ∂μ :=
  Iff.rfl

 
theorem HasWeakLineDerivOn.completeSpace (h : HasWeakLineDerivOn μ Ω u u' v) :
    CompleteSpace F := h.1

 
theorem HasWeakLineDerivOn.locallyIntegrableOn (h : HasWeakLineDerivOn μ Ω u u' v) :
    LocallyIntegrableOn u Ω μ := h.2.1

 
theorem HasWeakLineDerivOn.locallyIntegrableOn_deriv (h : HasWeakLineDerivOn μ Ω u u' v) :
    LocallyIntegrableOn u' Ω μ := h.2.2.1

 
theorem HasWeakLineDerivOn.integral_lineDeriv_smul_eq_neg_integral_smul
    (h : HasWeakLineDerivOn μ Ω u u' v) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ = -∫ x, (φ : E → ℝ) x • u' x ∂μ := h.2.2.2 φ

 






@[expose] def HasWeakFDerivOn (μ : Measure E) (Ω : Opens E) (u : E → F) (U : E → E →L[ℝ] F) : Prop :=
  ∀ v : E, HasWeakLineDerivOn μ Ω u (fun x => U x v) v

 


theorem hasWeakFDerivOn_iff {U : E → E →L[ℝ] F} :
    HasWeakFDerivOn μ Ω u U ↔
      ∀ v : E, HasWeakLineDerivOn μ Ω u (fun x => U x v) v :=
  Iff.rfl

 
theorem HasWeakFDerivOn.completeSpace {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    CompleteSpace F := (h 0).completeSpace

 
theorem HasWeakFDerivOn.locallyIntegrableOn {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    LocallyIntegrableOn u Ω μ := (h 0).locallyIntegrableOn

 



theorem hasWeakLineDerivOn_iff [CompleteSpace F] (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) :
    HasWeakLineDerivOn μ Ω u u' v ↔
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, lineDeriv ℝ φ x v • u x ∂μ = -∫ x, φ x • u' x ∂μ :=
  ⟨fun h φ hφ hφc hφs => h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hφc, hφs⟩,
    fun h =>
      ⟨‹CompleteSpace F›, hu, hu', fun φ => h φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset⟩⟩

 

theorem HasWeakLineDerivOn.mono {Ω' : Opens E} (h : HasWeakLineDerivOn μ Ω u u' v) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDerivOn μ Ω' u u' v :=
  ⟨h.completeSpace, h.locallyIntegrableOn.mono_set hΩ, h.locallyIntegrableOn_deriv.mono_set hΩ,
    fun φ => h.integral_lineDeriv_smul_eq_neg_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩⟩

 
theorem HasWeakFDerivOn.mono {U : E → E →L[ℝ] F} {Ω' : Opens E} (h : HasWeakFDerivOn μ Ω u U)
    (hΩ : Ω' ≤ Ω) : HasWeakFDerivOn μ Ω' u U := fun v => (h v).mono hΩ

 
theorem HasWeakFDerivOn.hasWeakLineDerivOn {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (v : E) : HasWeakLineDerivOn μ Ω u (fun x => U x v) v := h v

 



@[simp]
theorem hasWeakLineDerivOn_zero [CompleteSpace F] :
    HasWeakLineDerivOn μ Ω (0 : E → F) (0 : E → F) v :=
  ⟨‹CompleteSpace F›, locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun _ => by simp⟩

 
@[simp]
theorem hasWeakFDerivOn_zero [CompleteSpace F] : HasWeakFDerivOn μ Ω (0 : E → F) 0 :=
  fun _ => ⟨‹CompleteSpace F›, locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun _ => by simp⟩

 
theorem HasWeakLineDerivOn.neg (h : HasWeakLineDerivOn μ Ω u u' v) :
    HasWeakLineDerivOn μ Ω (-u) (-u') v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.neg, h.locallyIntegrableOn_deriv.neg, fun φ => ?_⟩
  simp only [Pi.neg_apply, smul_neg, integral_neg,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_neg]

 
theorem HasWeakFDerivOn.neg {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    HasWeakFDerivOn μ Ω (-u) (-U) := fun v => (h v).neg

 
theorem HasWeakLineDerivOn.const_smul (h : HasWeakLineDerivOn μ Ω u u' v) (c : ℝ) :
    HasWeakLineDerivOn μ Ω (c • u) (c • u') v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.smul c, h.locallyIntegrableOn_deriv.smul c,
    fun φ => ?_⟩
  simp only [Pi.smul_apply, smul_comm _ c, integral_smul,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, smul_neg]

 
theorem HasWeakFDerivOn.const_smul {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) (c : ℝ) :
    HasWeakFDerivOn μ Ω (c • u) (c • U) := fun v => (h v).const_smul c

end Defs

 

section Integrability

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {u u' : E → F}

 

theorem integrable_smul_of_locallyIntegrableOn {w : E → F} (hw : LocallyIntegrableOn w Ω μ)
    (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => (φ : E → ℝ) x • w x) μ := by
  simpa using TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ) hw φ

 

theorem integrable_lineDeriv_smul_of_locallyIntegrableOn {w : E → F}
    (hw : LocallyIntegrableOn w Ω μ) (φ : 𝓓(Ω, ℝ)) (v : E) :
    Integrable (fun x => lineDeriv ℝ (φ : E → ℝ) x v • w x) μ := by
  have hcoe : ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (φ : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  simpa [hcoe] using
    integrable_smul_of_locallyIntegrableOn hw (TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ))

omit [OpensMeasurableSpace E] in
 

theorem setIntegral_smul_eq_integral_smul {w : E → F} (φ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), (φ : E → ℝ) x • w x ∂μ = ∫ x, (φ : E → ℝ) x • w x ∂μ := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)]
  simp

omit [OpensMeasurableSpace E] in
 

theorem setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul {w : E → F} (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∫ x in (Ω : Set E), lineDeriv ℝ (φ : E → ℝ) x v • w x ∂μ =
      ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • w x ∂μ := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [lineDeriv_eq_zero_of_notMem_tsupport φ (fun hmem => hx (φ.tsupport_subset hmem)) v]
  simp

 

theorem HasWeakLineDerivOn.congr_ae {w : E → F} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hw : u =ᵐ[μ.restrict Ω] w) : HasWeakLineDerivOn μ Ω w u' v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.congr hw, h.locallyIntegrableOn_deriv,
    fun φ => ?_⟩
  rw [← h.integral_lineDeriv_smul_eq_neg_integral_smul φ]
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set E)
  · rw [hx hxΩ]
  · rw [lineDeriv_eq_zero_of_notMem_tsupport φ (fun h' => hxΩ (φ.tsupport_subset h')) v]
    simp

 

theorem HasWeakLineDerivOn.congr_ae_deriv {w : E → F} (h : HasWeakLineDerivOn μ Ω u u' v)
    (hw : u' =ᵐ[μ.restrict Ω] w) : HasWeakLineDerivOn μ Ω u w v := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn, h.locallyIntegrableOn_deriv.congr hw,
    fun φ => ?_⟩
  rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set E)
  · rw [hx hxΩ]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' => hxΩ (φ.tsupport_subset h'))]
    simp

 

theorem HasWeakFDerivOn.congr_ae {U : E → E →L[ℝ] F} {w : E → F} (h : HasWeakFDerivOn μ Ω u U)
    (hw : u =ᵐ[μ.restrict Ω] w) : HasWeakFDerivOn μ Ω w U := fun v => (h v).congr_ae hw

 

theorem HasWeakFDerivOn.congr_ae_deriv {U W : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hW : U =ᵐ[μ.restrict Ω] W) : HasWeakFDerivOn μ Ω u W := fun v =>
  (h v).congr_ae_deriv (hW.mono fun _ hx => congrArg (· v) hx)

 

theorem HasWeakLineDerivOn.indicator (h : HasWeakLineDerivOn μ Ω u u' v) :
    HasWeakLineDerivOn μ Ω ((Ω : Set E).indicator u) ((Ω : Set E).indicator u') v :=
  have hΩ : NullMeasurableSet (Ω : Set E) μ := Ω.isOpen.measurableSet.nullMeasurableSet
  (h.congr_ae (indicator_ae_eq_restrict hΩ).symm).congr_ae_deriv
    (indicator_ae_eq_restrict hΩ).symm

 

theorem HasWeakFDerivOn.indicator {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U) :
    HasWeakFDerivOn μ Ω ((Ω : Set E).indicator u) ((Ω : Set E).indicator U) :=
  have hΩ : NullMeasurableSet (Ω : Set E) μ := Ω.isOpen.measurableSet.nullMeasurableSet
  (h.congr_ae (indicator_ae_eq_restrict hΩ).symm).congr_ae_deriv
    (indicator_ae_eq_restrict hΩ).symm

end Integrability

 

section Linearity

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

 
theorem HasWeakLineDerivOn.add {u₁ u₁' u₂ u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u₁ u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u₂ u₂' v) :
    HasWeakLineDerivOn μ Ω (u₁ + u₂) (u₁' + u₂') v := by
  refine ⟨h₁.completeSpace, h₁.locallyIntegrableOn.add h₂.locallyIntegrableOn,
    h₁.locallyIntegrableOn_deriv.add h₂.locallyIntegrableOn_deriv, fun φ => ?_⟩
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • (u₁ + u₂) x ∂μ =
      (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₁ x ∂μ) +
        ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u₂ x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn φ v)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₂.locallyIntegrableOn φ v)
  have hright : ∫ x, (φ : E → ℝ) x • (u₁' + u₂') x ∂μ =
      (∫ x, (φ : E → ℝ) x • u₁' x ∂μ) + ∫ x, (φ : E → ℝ) x • u₂' x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn_deriv φ)
      (integrable_smul_of_locallyIntegrableOn h₂.locallyIntegrableOn_deriv φ)
  rw [hleft, hright, h₁.integral_lineDeriv_smul_eq_neg_integral_smul φ,
    h₂.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_add]

 
theorem HasWeakLineDerivOn.sub {u₁ u₁' u₂ u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u₁ u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u₂ u₂' v) :
    HasWeakLineDerivOn μ Ω (u₁ - u₂) (u₁' - u₂') v := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

 
theorem HasWeakLineDerivOn.sum {ι : Type*} [CompleteSpace F] {w w' : ι → E → F} (s : Finset ι)
    (h : ∀ i ∈ s, HasWeakLineDerivOn μ Ω (w i) (w' i) v) :
    HasWeakLineDerivOn μ Ω (fun x => ∑ i ∈ s, w i x) (fun x => ∑ i ∈ s, w' i x) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact hasWeakLineDerivOn_zero
  | insert a s ha ih =>
      have key := (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      have e : ∀ z : ι → E → F,
          (fun x => ∑ i ∈ insert a s, z i x) = z a + fun x => ∑ i ∈ s, z i x :=
        fun z => funext fun x => by simp [Finset.sum_insert ha]
      rw [e w, e w']
      exact key

 
theorem HasWeakLineDerivOn.clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (h : HasWeakLineDerivOn μ Ω u u' v) (L : F →L[ℝ] G) :
    HasWeakLineDerivOn μ Ω (fun x => L (u x)) (fun x => L (u' x)) v := by
  have := h.completeSpace
  have hcomp : ∀ w : E → F, LocallyIntegrableOn w Ω μ →
      LocallyIntegrableOn (fun x => L (w x)) Ω μ := by
    intro w hw x hx
    obtain ⟨t, ht, hint⟩ := hw x hx
    exact ⟨t, ht, L.integrable_comp hint⟩
  refine ⟨‹CompleteSpace G›, hcomp u h.locallyIntegrableOn,
    hcomp u' h.locallyIntegrableOn_deriv, fun φ => ?_⟩
  calc ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • L (u x) ∂μ
      = L (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u x ∂μ) := by
        rw [← ContinuousLinearMap.integral_comp_comm L
          (integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ v)]
        simp
    _ = L (-∫ x, (φ : E → ℝ) x • u' x ∂μ) := by
        rw [h.integral_lineDeriv_smul_eq_neg_integral_smul φ]
    _ = -∫ x, (φ : E → ℝ) x • L (u' x) ∂μ := by
        rw [map_neg]
        congr 1
        rw [← ContinuousLinearMap.integral_comp_comm L
          (integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φ)]
        simp

 
theorem HasWeakFDerivOn.add {u₁ u₂ : E → F} {U₁ U₂ : E → E →L[ℝ] F}
    (h₁ : HasWeakFDerivOn μ Ω u₁ U₁) (h₂ : HasWeakFDerivOn μ Ω u₂ U₂) :
    HasWeakFDerivOn μ Ω (u₁ + u₂) (U₁ + U₂) := fun v => (h₁ v).add (h₂ v)

 
theorem HasWeakFDerivOn.sub {u₁ u₂ : E → F} {U₁ U₂ : E → E →L[ℝ] F}
    (h₁ : HasWeakFDerivOn μ Ω u₁ U₁) (h₂ : HasWeakFDerivOn μ Ω u₂ U₂) :
    HasWeakFDerivOn μ Ω (u₁ - u₂) (U₁ - U₂) := fun v => (h₁ v).sub (h₂ v)

omit [OpensMeasurableSpace E] in
 
theorem hasWeakLineDerivOn_zero_direction [CompleteSpace F] {u : E → F}
    (hu : LocallyIntegrableOn u Ω μ) : HasWeakLineDerivOn μ Ω u (0 : E → F) 0 :=
  ⟨‹CompleteSpace F›, hu, locallyIntegrableOn_zero, fun φ => by simp [lineDeriv_zero]⟩

 



theorem HasWeakLineDerivOn.add_direction {u u₁' u₂' : E → F} {v₁ v₂ : E}
    (h₁ : HasWeakLineDerivOn μ Ω u u₁' v₁) (h₂ : HasWeakLineDerivOn μ Ω u u₂' v₂) :
    HasWeakLineDerivOn μ Ω u (u₁' + u₂') (v₁ + v₂) := by
  refine ⟨h₁.completeSpace, h₁.locallyIntegrableOn,
    h₁.locallyIntegrableOn_deriv.add h₂.locallyIntegrableOn_deriv, fun φ => ?_⟩
   
  have hsplit : ∀ x, lineDeriv ℝ (φ : E → ℝ) x (v₁ + v₂) =
      lineDeriv ℝ (φ : E → ℝ) x v₁ + lineDeriv ℝ (φ : E → ℝ) x v₂ := fun x => by
    have h := congrArg (fun T : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) => ((T φ : 𝓓(Ω, ℝ)) : E → ℝ) x)
      (TestFunction.lineDerivCLM_add (𝕜 := ℝ) (v₁ := v₁) (v₂ := v₂))
    simpa [TestFunction.lineDerivCLM_apply_of_le le_top] using h
  have hleft : ∫ x, lineDeriv ℝ (φ : E → ℝ) x (v₁ + v₂) • u x ∂μ =
      (∫ x, lineDeriv ℝ (φ : E → ℝ) x v₁ • u x ∂μ) +
        ∫ x, lineDeriv ℝ (φ : E → ℝ) x v₂ • u x ∂μ := by
    simp only [hsplit, add_smul]
    exact integral_add
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn φ v₁)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn φ v₂)
  have hright : ∫ x, (φ : E → ℝ) x • (u₁' + u₂') x ∂μ =
      (∫ x, (φ : E → ℝ) x • u₁' x ∂μ) + ∫ x, (φ : E → ℝ) x • u₂' x ∂μ := by
    simp only [Pi.add_apply, smul_add]
    exact integral_add (integrable_smul_of_locallyIntegrableOn h₁.locallyIntegrableOn_deriv φ)
      (integrable_smul_of_locallyIntegrableOn h₂.locallyIntegrableOn_deriv φ)
  rw [hleft, hright, h₁.integral_lineDeriv_smul_eq_neg_integral_smul φ,
    h₂.integral_lineDeriv_smul_eq_neg_integral_smul φ, neg_add]

 
theorem HasWeakLineDerivOn.sum_direction {ι : Type*} [CompleteSpace F] {u : E → F}
    {u' : ι → E → F} {w : ι → E} (s : Finset ι) (hu : LocallyIntegrableOn u Ω μ)
    (h : ∀ i ∈ s, HasWeakLineDerivOn μ Ω u (u' i) (w i)) :
    HasWeakLineDerivOn μ Ω u (fun x => ∑ i ∈ s, u' i x) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact hasWeakLineDerivOn_zero_direction hu
  | insert a s ha ih =>
      have key := (h a (Finset.mem_insert_self a s)).add_direction
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      have e : (fun x => ∑ i ∈ insert a s, u' i x) = u' a + fun x => ∑ i ∈ s, u' i x :=
        funext fun x => by simp [Finset.sum_insert ha]
      rw [e, Finset.sum_insert ha]
      exact key

end Linearity

 

section SmulDirection

variable [MeasurableSpace E] {μ : Measure E} {u u' : E → F}

 
theorem HasWeakLineDerivOn.smul_direction (h : HasWeakLineDerivOn μ Ω u u' v) (c : ℝ) :
    HasWeakLineDerivOn μ Ω u (c • u') (c • v) := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn, h.locallyIntegrableOn_deriv.smul c,
    fun φ => ?_⟩
  simp only [lineDeriv_smul, smul_eq_mul, mul_smul, integral_smul,
    h.integral_lineDeriv_smul_eq_neg_integral_smul φ, Pi.smul_apply, smul_comm _ c, smul_neg]

end SmulDirection

 

section Basis

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {u : E → F}

 




theorem _root_.Module.Basis.hasWeakFDerivOn_of_forall {ι : Type*} [CompleteSpace F]
    (b : Module.Basis ι ℝ E) {U : E → E →L[ℝ] F} (hu : LocallyIntegrableOn u Ω μ)
    (h : ∀ i, HasWeakLineDerivOn μ Ω u (fun x => U x (b i)) (b i)) :
    HasWeakFDerivOn μ Ω u U := by
  classical
  intro y
  have hy : ∑ i ∈ (b.repr y).support, b.repr y i • b i = y := by
    have hrepr := b.linearCombination_repr y
    rwa [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
  have key : HasWeakLineDerivOn μ Ω u
      (fun x => ∑ i ∈ (b.repr y).support, b.repr y i • U x (b i))
      (∑ i ∈ (b.repr y).support, b.repr y i • b i) :=
    HasWeakLineDerivOn.sum_direction _ hu fun i _ => by
      simpa [Pi.smul_def] using (h i).smul_direction (b.repr y i)
  have hval : ∀ x, (∑ i ∈ (b.repr y).support, b.repr y i • U x (b i)) = U x y := by
    intro x
    have hUy : U x y = U x (∑ i ∈ (b.repr y).support, b.repr y i • b i) := by rw [hy]
    rw [hUy, map_sum]
    simp
  rw [hy] at key
  exact key.congr_ae_deriv (Filter.Eventually.of_forall hval)

end Basis

 





section Classical

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u u' : E → F}

 






theorem hasWeakLineDerivOn_of_hasLineDerivAt (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn u' Ω μ) (h : ∀ x ∈ (Ω : Set E), HasLineDerivAt ℝ u (u' x) x v) :
    HasWeakLineDerivOn μ Ω u u' v := by
  refine ⟨‹CompleteSpace F›, hu, hu', fun φ => ?_⟩
  have hφd := φ.contDiff.differentiable (by simp)
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (f := u) (f' := u') (g := (φ : E → ℝ))
    (g' := fun x => lineDeriv ℝ (φ : E → ℝ) x v) (v := v)
    (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip)
    (by simpa using integrable_smul_of_locallyIntegrableOn hu' φ)
    (by simpa using integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ v)
    (by simpa using integrable_smul_of_locallyIntegrableOn hu φ)
    (fun x hx => h x (φ.tsupport_subset hx))
    (fun x _ => (hφd x).lineDifferentiableAt.hasLineDerivAt)
  simpa using key

 



theorem hasWeakLineDerivOn_const (c : F) :
    HasWeakLineDerivOn μ Ω (fun _ => c) (fun _ => 0) v :=
  hasWeakLineDerivOn_of_hasLineDerivAt (locallyIntegrableOn_const c) locallyIntegrableOn_zero
    fun x _ => (hasFDerivAt_const c x).hasLineDerivAt v

 


theorem hasWeakFDerivOn_of_differentiableOn (hu : LocallyIntegrableOn u Ω μ)
    (hu' : LocallyIntegrableOn (fderiv ℝ u) Ω μ)
    (h : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ u x) :
    HasWeakFDerivOn μ Ω u (fderiv ℝ u) := fun v =>
  hasWeakLineDerivOn_of_hasLineDerivAt hu
    (by
      simpa [Function.comp_def] using
        (ContinuousLinearMap.apply ℝ F v).locallyIntegrableOn_comp hu')
    fun x hx => (h x hx).hasFDerivAt.hasLineDerivAt v

end Classical

 





section TestFunction

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

open scoped Gradient InnerProductSpace

 

theorem hasWeakFDerivOn_testFunction (φ : 𝓓(Ω, ℝ)) :
    HasWeakFDerivOn μ Ω (φ : E → ℝ) fun x => innerSL ℝ (∇ (φ : E → ℝ) x) := by
  have hcoe : (fun x => innerSL ℝ (∇ (φ : E → ℝ) x)) = fderiv ℝ (φ : E → ℝ) := by
    funext x
    ext y
    simp [inner_gradient_left (𝕜 := ℝ) (f := (φ : E → ℝ)) (x := x) (y := y)]
  rw [hcoe]
  refine hasWeakFDerivOn_of_differentiableOn ?_ ?_ fun x _ =>
    (φ.contDiff.differentiable (by simp)) x
  · exact φ.continuous.locallyIntegrable.locallyIntegrableOn _
  · exact (φ.contDiff.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _

end TestFunction

 

section Uniqueness

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} {u : E → F}

 






theorem HasWeakLineDerivOn.ae_eq {u₁' u₂' : E → F} (h₁ : HasWeakLineDerivOn μ Ω u u₁' v)
    (h₂ : HasWeakLineDerivOn μ Ω u u₂' v) : u₁' =ᵐ[μ.restrict Ω] u₂' := by
  have := h₁.completeSpace
  have hu₁ := h₁.locallyIntegrableOn_deriv
  have hu₂ := h₂.locallyIntegrableOn_deriv
  have key : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ (Ω : Set E) →
      ∫ x, φ x • (u₁' - u₂') x ∂μ = 0 := by
    intro φ hφ hφc hφs
    have hi₁ : Integrable (fun x => φ x • u₁' x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu₁ (⟨φ, hφ, hφc, hφs⟩ : 𝓓(Ω, ℝ))
    have hi₂ : Integrable (fun x => φ x • u₂' x) μ := by
      simpa using integrable_smul_of_locallyIntegrableOn hu₂ (⟨φ, hφ, hφc, hφs⟩ : 𝓓(Ω, ℝ))
    have hsame : ∫ x, φ x • u₁' x ∂μ = ∫ x, φ x • u₂' x ∂μ := by
      have hneg := (h₁.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hφc, hφs⟩).symm.trans
        (h₂.integral_lineDeriv_smul_eq_neg_integral_smul ⟨φ, hφ, hφc, hφs⟩)
      simpa using neg_injective hneg
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub hi₁ hi₂, hsame, sub_self]
  have hzero := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hu₁.sub hu₂) key
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [hzero] with x hx hxΩ
  simpa [sub_eq_zero] using hx hxΩ

 




theorem HasWeakFDerivOn.ae_eq {U₁ U₂ : E → E →L[ℝ] F} (h₁ : HasWeakFDerivOn μ Ω u U₁)
    (h₂ : HasWeakFDerivOn μ Ω u U₂) : U₁ =ᵐ[μ.restrict Ω] U₂ := by
  set b := Module.finBasis ℝ E
  have hcoord : ∀ i, (fun x => U₁ x (b i)) =ᵐ[μ.restrict Ω] fun x => U₂ x (b i) :=
    fun i => (h₁ (b i)).ae_eq (h₂ (b i))
  filter_upwards [Filter.eventually_all.2 hcoord] with x hx
  exact ContinuousLinearMap.coe_injective (b.ext fun i => hx i)

end Uniqueness

 

section Comparison

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {u u' : E → F}

 







theorem HasWeakLineDerivOn.ae_eq_lineDeriv (h : HasWeakLineDerivOn μ Ω u u' v)
    (hd : LocallyIntegrableOn (fun x => lineDeriv ℝ u x v) Ω μ)
    (hdiff : ∀ x ∈ (Ω : Set E), LineDifferentiableAt ℝ u x v) :
    u' =ᵐ[μ.restrict Ω] fun x => lineDeriv ℝ u x v :=
  have := h.completeSpace
  h.ae_eq (hasWeakLineDerivOn_of_hasLineDerivAt h.locallyIntegrableOn hd
    fun x hx => (hdiff x hx).hasLineDerivAt)

 



theorem HasWeakFDerivOn.ae_eq_fderiv {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hd : LocallyIntegrableOn (fderiv ℝ u) Ω μ)
    (hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ u x) :
    U =ᵐ[μ.restrict Ω] fderiv ℝ u :=
  have := h.completeSpace
  h.ae_eq (hasWeakFDerivOn_of_differentiableOn h.locallyIntegrableOn hd hdiff)

end Comparison

end TauCeti
