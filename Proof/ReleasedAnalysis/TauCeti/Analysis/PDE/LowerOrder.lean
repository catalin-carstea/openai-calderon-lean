/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Mul

/-! From Proof/TauCeti/Analysis/PDE/LowerOrder.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 
























public section

namespace TauCeti

namespace PDE

open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

 
@[expose] noncomputable def driftForm (b : EuclideanSpace ℝ n) :
    ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ n) ℝ (innerSL ℝ b)

 
@[expose] noncomputable def massForm (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  c • ContinuousLinearMap.mul ℝ ℝ

 
@[simp]
lemma driftForm_apply (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    driftForm b u ξ = ⟪b, ξ⟫_ℝ * u := by
  rw [driftForm, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]

 
@[simp]
lemma massForm_apply (c u v : ℝ) :
    massForm c u v = c * u * v := by
  rw [massForm, smul_apply, smul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul]
  ring

 

 
@[expose] noncomputable def driftFormLinear :
    EuclideanSpace ℝ n →L[ℝ] ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  (ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ n) ℝ).comp (innerSL ℝ)

 
@[simp]
lemma driftFormLinear_apply (b : EuclideanSpace ℝ n) :
    driftFormLinear (n := n) b = driftForm b :=
  by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro ξ
    simp [driftFormLinear, driftForm]

 
lemma continuous_driftForm :
    Continuous (fun b : EuclideanSpace ℝ n => driftForm b) :=
  (driftFormLinear (n := n)).continuous.congr fun b => (driftFormLinear_apply b)

 
@[expose] noncomputable def massFormLinear : ℝ →L[ℝ] ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (ContinuousLinearMap.mul ℝ ℝ)

 
@[simp]
lemma massFormLinear_apply (c : ℝ) :
    massFormLinear c = massForm c :=
  by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp [massFormLinear, massForm]

 
lemma continuous_massForm : Continuous (fun c : ℝ => massForm c) :=
  massFormLinear.continuous.congr fun c => massFormLinear_apply c

section Continuity

variable {X : Type*} [TopologicalSpace X]

namespace Continuous

 
lemma driftForm {b : X → EuclideanSpace ℝ n} (hb : Continuous b) :
    Continuous (fun x => PDE.driftForm (b x)) :=
  continuous_driftForm.comp hb

 
lemma massForm {c : X → ℝ} (hc : Continuous c) :
    Continuous (fun x => PDE.massForm (c x)) :=
  continuous_massForm.comp hc

end Continuous

namespace ContinuousOn

 

lemma driftForm {s : Set X} {b : X → EuclideanSpace ℝ n} (hb : ContinuousOn b s) :
    ContinuousOn (fun x => PDE.driftForm (b x)) s :=
  continuous_driftForm.comp_continuousOn hb

 

lemma massForm {s : Set X} {c : X → ℝ} (hc : ContinuousOn c s) :
    ContinuousOn (fun x => PDE.massForm (c x)) s :=
  continuous_massForm.comp_continuousOn hc

end ContinuousOn

end Continuity

 

 
lemma norm_driftForm_apply_le (b : EuclideanSpace ℝ n) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm b u ξ‖ ≤ ‖b‖ * ‖u‖ * ‖ξ‖ := by
  rw [driftForm_apply, norm_mul]
  calc
    ‖⟪b, ξ⟫_ℝ‖ * ‖u‖ ≤ (‖b‖ * ‖ξ‖) * ‖u‖ := by
      gcongr
      exact norm_inner_le_norm b ξ
    _ = ‖b‖ * ‖u‖ * ‖ξ‖ := by ring

 
lemma norm_driftForm_apply_le_of_norm_le {b : EuclideanSpace ℝ n} {β : ℝ}
    (hb : ‖b‖ ≤ β) (u : ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖driftForm b u ξ‖ ≤ β * ‖u‖ * ‖ξ‖ := by
  exact (norm_driftForm_apply_le b u ξ).trans <| by
    gcongr

grind_pattern norm_driftForm_apply_le_of_norm_le =>
  ‖b‖ ≤ β, driftForm b u ξ

 
lemma opNorm_driftForm_le (b : EuclideanSpace ℝ n) :
    ‖driftForm b‖ ≤ ‖b‖ := by
  refine (driftForm b).opNorm_le_bound₂ (norm_nonneg b) ?_
  intro u ξ
  exact norm_driftForm_apply_le b u ξ

 

lemma opNorm_driftForm_le_of_norm_le {b : EuclideanSpace ℝ n} {β : ℝ} (hb : ‖b‖ ≤ β) :
    ‖driftForm b‖ ≤ β :=
  (opNorm_driftForm_le b).trans hb

grind_pattern opNorm_driftForm_le_of_norm_le =>
  ‖b‖ ≤ β, ‖driftForm b‖

 
lemma norm_driftForm_apply_le_of_norm_le_of_le {b : EuclideanSpace ℝ n}
    {β R S : ℝ} (hb : ‖b‖ ≤ β) {u : ℝ} {ξ : EuclideanSpace ℝ n} (hu : ‖u‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖driftForm b u ξ‖ ≤ β * R * S :=
  (driftForm b).le_of_opNorm₂_le_of_le (opNorm_driftForm_le_of_norm_le hb) hu hξ

grind_pattern norm_driftForm_apply_le_of_norm_le_of_le =>
  ‖b‖ ≤ β, ‖u‖ ≤ R, ‖ξ‖ ≤ S, driftForm b u ξ

 

 
lemma norm_massForm_apply_le (c u v : ℝ) :
    ‖massForm c u v‖ ≤ ‖c‖ * ‖u‖ * ‖v‖ := by
  rw [massForm_apply, norm_mul, norm_mul]

 
lemma norm_massForm_apply_le_of_norm_le {c γ : ℝ} (hc : ‖c‖ ≤ γ) (u v : ℝ) :
    ‖massForm c u v‖ ≤ γ * ‖u‖ * ‖v‖ := by
  exact (norm_massForm_apply_le c u v).trans <| by
    gcongr

grind_pattern norm_massForm_apply_le_of_norm_le =>
  ‖c‖ ≤ γ, massForm c u v

 
lemma opNorm_massForm_le (c : ℝ) :
    ‖massForm c‖ ≤ ‖c‖ := by
  refine (massForm c).opNorm_le_bound₂ (norm_nonneg c) ?_
  intro u v
  exact norm_massForm_apply_le c u v

 

lemma opNorm_massForm_le_of_norm_le {c γ : ℝ} (hc : ‖c‖ ≤ γ) :
    ‖massForm c‖ ≤ γ :=
  (opNorm_massForm_le c).trans hc

grind_pattern opNorm_massForm_le_of_norm_le =>
  ‖c‖ ≤ γ, ‖massForm c‖

 
lemma norm_massForm_apply_le_of_norm_le_of_le {c γ R S : ℝ} (hc : ‖c‖ ≤ γ)
    {u v : ℝ} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ S) :
    ‖massForm c u v‖ ≤ γ * R * S :=
  (massForm c).le_of_opNorm₂_le_of_le (opNorm_massForm_le_of_norm_le hc) hu hv

grind_pattern norm_massForm_apply_le_of_norm_le_of_le =>
  ‖c‖ ≤ γ, ‖u‖ ≤ R, ‖v‖ ≤ S, massForm c u v

end PDE

end TauCeti
