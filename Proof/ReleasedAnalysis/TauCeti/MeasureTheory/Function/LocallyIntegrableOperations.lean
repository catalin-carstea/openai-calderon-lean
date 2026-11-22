/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Relative-integrability lemmas from Tau Ceti revision
4d91513e4d30746eb1fa96658c18e051c772e55e as released with
arxiv-2610.13592-lean revision 4cfcab036aedbb4f825a3aeb366da12fe5673ddd. -/

public section

open Set
open scoped Topology

namespace MeasureTheory

/-- A finite sum of functions locally integrable on a set is locally integrable on it. This is the
local form of `MeasureTheory.locallyIntegrable_finsetSum`. -/
theorem locallyIntegrableOn_finsetSum {X F ι : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [NormedAddCommGroup F] {μ : Measure X} {s : Set X} (t : Finset ι) {f : ι → X → F}
    (hf : ∀ i ∈ t, LocallyIntegrableOn (f i) s μ) :
    LocallyIntegrableOn (fun x => ∑ i ∈ t, f i x) s μ := by
  simpa only [← Finset.sum_apply] using Finset.sum_induction f
    (fun g => LocallyIntegrableOn g s μ) (fun _ _ => LocallyIntegrableOn.add)
    (fun _ _ => ⟨univ, Filter.univ_mem, integrableOn_zero⟩) hf

end MeasureTheory

namespace MeasureTheory.LocallyIntegrableOn

variable {X E 𝕜 : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {μ : Measure X} {s : Set X} {f : X → 𝕜} {g : X → E}

/-- If `f` is locally integrable on `s` and `g` is continuous with compact support contained in
`s`, then `f • g` is integrable. This is the relative form of Mathlib's
`LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`. -/
theorem integrable_smul_right_of_hasCompactSupport (hf : LocallyIntegrableOn f s μ)
    (hg : Continuous g) (h'g : HasCompactSupport g) (hgs : tsupport g ⊆ s) :
    Integrable (fun x ↦ f x • g x) μ := by
  have : (tsupport g).indicator (fun x ↦ f x • g x) = fun x ↦ f x • g x :=
    indicator_eq_self.2 <| Function.support_subset_iff'.2 fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this, indicator_smul_left]
  refine Integrable.smul_of_top_left ?_ (hg.memLp_top_of_hasCompactSupport h'g μ)
  rw [integrable_indicator_iff (isClosed_tsupport g).measurableSet]
  exact hf.integrableOn_compact_subset hgs h'g

/-- If `f` is locally integrable on `s` and `g` is continuous with compact support contained in
`s`, then `g • f` is integrable. This is the relative form of Mathlib's
`LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`. -/
theorem integrable_smul_left_of_hasCompactSupport {f : X → E} {g : X → 𝕜}
    (hf : LocallyIntegrableOn f s μ) (hg : Continuous g) (h'g : HasCompactSupport g)
    (hgs : tsupport g ⊆ s) : Integrable (fun x ↦ g x • f x) μ := by
  have : (tsupport g).indicator (fun x ↦ g x • f x) = fun x ↦ g x • f x :=
    indicator_eq_self.2 <| Function.support_subset_iff'.2 fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← this, indicator_smul]
  refine Integrable.smul_of_top_right ?_ (hg.memLp_top_of_hasCompactSupport h'g μ)
  rw [integrable_indicator_iff (isClosed_tsupport g).measurableSet]
  exact hf.integrableOn_compact_subset hgs h'g

end MeasureTheory.LocallyIntegrableOn
