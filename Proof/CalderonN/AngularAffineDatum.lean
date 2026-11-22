module

public import Proof.CalderonN.CompactFiniteJets
public import Proof.CalderonN.SphereFrame

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Adapted from `AngularAffineDatum` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1400000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A smooth angular datum on a neighborhood of the sphere carries its
jets unchanged into a global representative. -/
theorem exists_angularAffineDatum_extension
    (n : ℕ) (a : ℝ) {U : Set (X dim)} (hU : IsOpen U) (hSU : (standardSphere dim) ⊆ U)
    {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (M J : ℝ)
    (hM : 0 ≤ M)
    (hJ : ∀ z ∈ (standardSphere dim), ∀ k ≤ n, ‖iteratedFDeriv ℝ k (fun _ : (X dim) => (1:ℝ)) z‖ ≤ J)
    (h : ∀ z ∈ (standardSphere dim), ∀ k ≤ n, ‖iteratedFDeriv ℝ k f z‖ ≤ M) :
    ∃ F : (X dim) → ℝ, ContDiff ℝ ∞ F ∧ ∀ z ∈ (standardSphere dim),
      F =ᶠ[𝓝 z] (fun z => a*f z-1) ∧
      ∀ k ≤ n, ‖iteratedFDeriv ℝ k F z‖ ≤ |a| * M+J := by
  obtain ⟨u,hu,_,W,hW,hSW,_,he⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_sphere (0 : (X dim)) 1 : IsCompact (standardSphere dim)) hSU hf
  let L : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
  let F := L ∘ u - fun _ : (X dim) => (1:ℝ)
  have hL : ‖L‖ ≤ |a| := by
    rw [show L = a • ContinuousLinearMap.id ℝ ℝ from rfl,norm_smul,Real.norm_eq_abs,
      ContinuousLinearMap.norm_id,mul_one]
  have hF : ContDiff ℝ ∞ F := (L.contDiff.comp hu).sub contDiff_const
  refine ⟨F,hF,?_⟩
  intro z hz
  have hE : u =ᶠ[𝓝 z] f := by
    filter_upwards [hW.mem_nhds (hSW hz)] with x hx using he hx
  refine ⟨?_,?_⟩
  · filter_upwards [hE] with x hx
    change a*u x-1 = a*f x-1
    rw [hx]
  · intro k hk
    change ‖iteratedFDeriv ℝ k (L ∘ u - fun _ : (X dim) => (1:ℝ)) z‖ ≤ _
    rw [iteratedFDeriv_sub ((L.contDiff.comp hu).of_le (by simp))
      (contDiff_const (c := (1:ℝ)))]
    have h₁ := L.norm_iteratedFDeriv_comp_left (n := k) (x := z) hu.contDiffAt (by simp)
    have h₂ : ‖iteratedFDeriv ℝ k u z‖ ≤ M := by
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hE k).eq_of_nhds]
      exact h z hz k hk
    exact (norm_sub_le _ _).trans (add_le_add (h₁.trans
      (mul_le_mul hL h₂ (norm_nonneg _) (abs_nonneg _))) (hJ z hz k hk))

end CalderonN
