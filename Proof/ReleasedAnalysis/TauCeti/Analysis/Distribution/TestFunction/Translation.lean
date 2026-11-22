/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction

/-! From Proof/TauCeti/Analysis/Distribution/TestFunction/Translation.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 













public section

noncomputable section

namespace TauCeti

open Set TopologicalSpace
open scoped Distributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Omega V : Opens E} {h : E}

 

@[expose] def translateTestFunction (hVO : MapsTo (· + h) V Omega) (phi : 𝓓(V, ℝ)) :
    𝓓(Omega, ℝ) :=
  ⟨fun y => phi (y - h),
    phi.contDiff.comp (contDiff_id.sub contDiff_const),
    by
      simpa [sub_eq_add_neg, Function.comp_def, Homeomorph.addRight] using
        phi.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-h)),
    by
      intro y hy
      have hy' : y + -h ∈ tsupport (phi : E → ℝ) := by
        have hfun : (fun z => phi (z - h)) =
            (phi : E → ℝ) ∘ (Homeomorph.addRight (-h) : E → E) := by
          funext z
          simp only [Function.comp_apply, sub_eq_add_neg]
          apply congrArg phi
          rfl
        have hycomp : y ∈ tsupport
            ((phi : E → ℝ) ∘ (Homeomorph.addRight (-h) : E → E)) := by
          rw [← hfun]
          exact hy
        rw [tsupport_comp_eq_preimage] at hycomp
        exact hycomp
      simpa only [sub_eq_add_neg, neg_add_cancel_right] using hVO (phi.tsupport_subset hy')⟩

 
@[simp]
theorem translateTestFunction_apply (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, ℝ)) (y : E) : translateTestFunction hVO phi y = phi (y - h) :=
  (rfl)

 

@[simp]
theorem lineDeriv_translateTestFunction (hVO : MapsTo (· + h) V Omega)
    (phi : 𝓓(V, ℝ)) (y w : E) :
    lineDeriv ℝ (translateTestFunction hVO phi : E → ℝ) y w =
      lineDeriv ℝ (phi : E → ℝ) (y - h) w := by
  simp only [lineDeriv, translateTestFunction_apply, sub_eq_add_neg]
  congr 1
  funext t
  congr 1
  abel

end TauCeti
