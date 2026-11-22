/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
 
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! From Proof/TauCeti/Analysis/Calculus/Gradient.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 


























public section

namespace TauCeti

open InnerProductSpace

open scoped ComplexConjugate Gradient

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F] {f g : F → 𝕜} {x : F}

 

theorem norm_gradient_eq_norm_fderiv (f : F → 𝕜) (x : F) : ‖∇ f x‖ = ‖fderiv 𝕜 f x‖ :=
  (toDual 𝕜 F).symm.norm_map _

 
theorem gradient_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    ∇ (f + g) x = ∇ f x + ∇ g x := by
  apply (toDual 𝕜 F).injective
  simp only [toDual_gradient, map_add, fderiv_add hf hg]

 

theorem gradient_const_smul (c : 𝕜) :
    ∇ (c • f) x = conj c • ∇ f x := by
  apply (toDual 𝕜 F).injective
  simp only [toDual_gradient, map_smulₛₗ, RingHomCompTriple.comp_apply, RingHom.id_apply,
    fderiv_const_smul_field, Pi.smul_apply]

 

@[simp]
theorem gradient_of_notMem_tsupport (h : x ∉ tsupport f) : ∇ f x = 0 := by
  rw [gradient, fderiv_of_notMem_tsupport 𝕜 h, map_zero]

 


@[fun_prop]
theorem measurable_gradient [MeasurableSpace F] [BorelSpace F] (f : F → 𝕜) : Measurable (∇ f) := by
  have h : ∇ f = (toDual 𝕜 F).symm ∘ fderiv 𝕜 f := by
    ext1 x
    rw [Function.comp_apply, ← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  rw [h]
  exact (toDual 𝕜 F).symm.continuous.measurable.comp (measurable_fderiv 𝕜 f)

 

theorem _root_.ContDiff.gradient_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {m n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (∇ f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)

end TauCeti
