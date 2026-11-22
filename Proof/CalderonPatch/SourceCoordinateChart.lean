module

public import Proof.CalderonPatch.InteriorChartBasis

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- A smooth tuple of source values with invertible differential is an
interior coordinate chart after restriction. -/
theorem exists_chart_of_invertible_mfderiv {f : M → X n} {p : M} {U : Set M}
    (hp : p ∈ (𝓡∂ n).interior M) (hU : IsOpen U) (hpU : p ∈ U)
    (hf : ContMDiffOn J K ∞ f U) (hInv : (mfderiv J K f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph M (X n),
      p ∈ e.source ∧ e.source ⊆ U ∧ e.source ⊆ (𝓡∂ n).interior M ∧
      EqOn e f e.source ∧ ContMDiffOn J K ∞ e e.source ∧
      ContMDiffOn K J ∞ e.symm e.target := by
  obtain ⟨c, hpc, hcU, hcI, hc, hcs⟩ := exists_interiorChart p hp hU hpU
  let F : X n → X n := f ∘ c.symm
  let z := c p
  have hz : z ∈ c.target := c.map_source hpc
  have hcz : c.symm z = p := c.left_inv hpc
  have hF : ContDiffOn ℝ ∞ F c.target :=
    (hf.comp hcs (fun _ hx => hcU (c.map_target hx))).contDiffOn
  have hFz := hF.contDiffAt (c.open_target.mem_nhds hz)
  have hcD : c.MDifferentiable J K :=
    ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩
  have hInvF : (fderiv ℝ F z).IsInvertible := by
    have hInvC : (mfderiv K J c.symm z).IsInvertible := ⟨hcD.symm.mfderiv hz, rfl⟩
    have hDf : MDifferentiableAt J K f (c.symm z) := by
      rw [hcz]
      exact (hf.contMDiffAt (hU.mem_nhds hpU)).mdifferentiableAt (by simp)
    have hInv' : (mfderiv J K f (c.symm z)).IsInvertible := hcz.symm ▸ hInv
    have hmf : mfderiv K K F z = fderiv ℝ F z := by
      rw [mfderiv_eq_fderiv]
      ext x
      rfl
    rw [← hmf, mfderiv_comp z hDf (hcD.mdifferentiableAt_symm hz)]
    exact hInv'.comp hInvC
  obtain ⟨B, hB⟩ := hInvF
  have hF' : HasFDerivAt F (B : X n →L[ℝ] X n) z :=
    hB ▸ (hFz.differentiableAt (by simp)).hasFDerivAt
  let k := hFz.toOpenPartialHomeomorph F hF' (by simp)
  have hzk : z ∈ k.source := hFz.mem_toOpenPartialHomeomorph_source hF' (by simp)
  let V := c.target ∩ (fderiv ℝ F) ⁻¹' {A | ContinuousLinearMap.IsInvertible A}
  have hV : IsOpen V :=
    (hF.continuousOn_fderiv_of_isOpen c.open_target (by simp)).isOpen_inter_preimage
      c.open_target ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let k' := k.restr V
  have hk'src : k'.source = k.source ∩ V := k.restr_source' V hV
  have hkC : k'.source ⊆ c.target := fun _ hx => (show _ ∈ k.source ∩ V from hk'src ▸ hx).2.1
  have hzk' : z ∈ k'.source := hk'src.symm ▸ ⟨hzk, hz, ⟨B, hB⟩⟩
  have hk' : ContMDiffOn K K ∞ k' k'.source := (hF.mono hkC).contMDiffOn
  have hk's : ContMDiffOn K K ∞ k'.symm k'.target := by
    apply (contMDiffOn_iff_contDiffOn).mpr
    intro y hy
    have hx := k'.map_target hy
    have hxC := hkC hx
    have hF' := hF.contDiffAt (c.open_target.mem_nhds hxC)
    obtain ⟨A, hA⟩ := (show k'.symm y ∈ k.source ∩ V from hk'src ▸ hx).2.2
    exact (k'.contDiffAt_symm hy (hA ▸ (hF'.differentiableAt (by simp)).hasFDerivAt) hF').contDiffWithinAt
  let e := c.trans k'
  have hec : e.source ⊆ c.source := fun _ hx => hx.1
  have hes : MapsTo c e.source k'.source := fun _ hx => hx.2
  have het : e.target ⊆ k'.target := fun _ hy => hy.1
  have hes' : MapsTo k'.symm e.target c.target := fun _ hy => hy.2
  refine ⟨e, ⟨hpc, hzk'⟩, hec.trans hcU, hec.trans hcI, ?_,
    hk'.comp (hc.mono hec) hes, hcs.comp (hk's.mono het) hes'⟩
  intro x hx
  change f (c.symm (c x)) = f x
  rw [c.left_inv (hec hx)]

end CalderonPatch
