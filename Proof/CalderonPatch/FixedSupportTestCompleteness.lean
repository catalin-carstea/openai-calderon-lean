module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.LocallyConvex.Barrelled

import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.UniformSpace.Pi

public section

noncomputable section
open Filter Function Set Topology TopologicalSpace
open scoped BoundedContinuousFunction ContDiff Distributions Uniformity

namespace CalderonPatch

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)

local notation "D" => 𝓓_{K}(E, F)
local notation "B" j => (E [×j]→L[ℝ] F)
private def derivatives : D →L[ℝ] (Π j : ℕ, E →ᵇ B j) :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)

private theorem derivatives_apply (u : D) (j : ℕ) :
    (derivatives K u j : E → B j) = iteratedFDeriv ℝ j u :=
  ContDiffMapSupportedIn.structureMapCLM_top_apply ℝ u

set_option backward.isDefEq.respectTransparency false in
/-- A uniform limit of every derivative is again the derivative sequence
of a single smooth function with the same compact support. -/
private theorem isClosed_range_derivatives : IsClosed (range (derivatives (F := F) K)) := by
  apply closure_subset_iff_isClosed.mp
  intro H hH
  let l : Filter D := comap (derivatives K) (𝓝 H)
  have : l.NeBot := Filter.comap_neBot fun s hs => by
    obtain ⟨_, hy, u, rfl⟩ := mem_closure_iff_nhds.mp hH s hs
    exact ⟨u,hy⟩
  have hT : Tendsto (derivatives K) l (𝓝 H) := tendsto_comap
  have hDeriv (j : ℕ) : TendstoUniformly (fun u : D => iteratedFDeriv ℝ j u) (H j) l := by
    have hj := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (tendsto_pi_nhds.mp hT j)
    simpa only [derivatives_apply] using hj
  let f (x : E) : F := (H 0 x).curry0
  let p (x : E) : FormalMultilinearSeries ℝ E F := fun j => H j x
  have hp : HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) f p univ := by
    refine ⟨fun _ _ => rfl,fun j hj x _ => ?_,fun j _ => (H j).continuous.continuousOn⟩
    rw [hasFDerivWithinAt_univ]
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) F).toLinearIsometry
    have hCurry : TendstoUniformly
        (fun (u : D) t => L (iteratedFDeriv ℝ (j+1) u t)) (fun t => L (H (j+1) t)) l :=
      L.isometry.uniformContinuous.comp_tendstoUniformly (hDeriv (j+1))
    apply hasFDerivAt_of_tendstoUniformly hCurry ?_ (hDeriv j).tendsto_at x
    intro u y
    have hd := u.contDiff.differentiable_iteratedFDeriv hj y
    convert hd.hasFDerivAt using 1
    simp [L, fderiv_iteratedFDeriv]
  have hf : ContDiff ℝ ∞ f := contDiffOn_univ.mp hp.contDiffOn
  have hfK (x : E) (hx : x ∉ K) : f x = 0 := by
    have h0 := (hDeriv 0).tendsto_at x
    let ev : (B 0) →L[ℝ] F := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) F 0
    have hE := ev.continuous.tendsto (H 0 x) |>.comp h0
    have hSource : (fun u : D => ev (iteratedFDeriv ℝ 0 u x)) = fun _ => (0 : F) := by
      funext u
      change iteratedFDeriv ℝ 0 u x (0 : Fin 0 → E) = 0
      rw [iteratedFDeriv_zero_apply]
      exact u.zero_on_compl hx
    have hF : Tendsto (fun u : D => ev (iteratedFDeriv ℝ 0 u x)) l (𝓝 (f x)) := hE
    rw [hSource] at hF
    exact tendsto_nhds_unique hF tendsto_const_nhds
  let u : D := ⟨f,hf,hfK⟩
  refine ⟨u,?_⟩
  funext j
  ext x : 1
  change (derivatives K u j : E → B j) x = H j x
  rw [derivatives_apply,← iteratedFDerivWithin_univ]
  exact (hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (by simp) uniqueDiffOn_univ (mem_univ x)).symm

/-- The ordinary fixed-compact-support test space is complete in its
usual topology of uniform convergence of all derivatives. -/
theorem fixedSupportTest_completeSpace [CompleteSpace F] : CompleteSpace D := by
  apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ (E := E) (F := F)
    (n := ⊤) (K := K)).isUniformInducing.completeSpace
  exact (isClosed_range_derivatives (F := F) K).isComplete

/-- The resulting test space carries the Baire property used in uniform
boundedness arguments for distributions. -/
theorem fixedSupportTest_baireSpace [CompleteSpace F] : BaireSpace D := by
  let e := ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ (E := E) (F := F)
    (n := ⊤) (K := K)
  let : CompleteSpace D := fixedSupportTest_completeSpace K
  let : (𝓤 D).IsCountablyGenerated := by
    rw [← e.isUniformInducing.comap_uniformity]
    infer_instance
  infer_instance

end CalderonPatch
