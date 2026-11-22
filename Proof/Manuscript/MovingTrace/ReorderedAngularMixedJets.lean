module

public import Proof.Manuscript.MovingTrace.MixedResidualSliceJets
public import Proof.Manuscript.AnnulusJets
public import Proof.CalderonN.CompactSmoothExtension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {P E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem angularMixedJet_congr_germ
    {f g : P → E → V} {p : P} {ξ : E}
    (he : Function.uncurry f =ᶠ[𝓝 (p,ξ)] Function.uncurry g) (j l : ℕ) :
    angularMixedJet j l f p ξ = angularMixedJet j l g p ξ := by
  obtain ⟨U,hU,W,hW,hUW⟩ := mem_nhds_prod_iff.mp he
  have hOuter : (fun a => iteratedFDeriv ℝ l (f a) ξ) =ᶠ[𝓝 p]
      (fun a => iteratedFDeriv ℝ l (g a) ξ) := by
    filter_upwards [hU] with a ha
    have hInner : f a =ᶠ[𝓝 ξ] g a :=
      Filter.mem_of_superset hW (fun z hz => hUW (show (a,z) ∈ U ×ˢ W from ⟨ha,hz⟩))
    exact (hInner.iteratedFDeriv ℝ l).eq_of_nhds
  exact (hOuter.iteratedFDeriv ℝ j).eq_of_nhds

/-- Put the frequency first in the trial coordinates, then move it to
the last slot where the symbol seminorms differentiate it first. -/
theorem norm_angularMixedJet_le_reordered_joint
    {O : Set ((P × E) × E)} (hO : IsOpen O)
    {F : (P × E) × E → V} (hF : ContDiffOn ℝ ∞ F O)
    (p : P) (x ξ : E) (hq : ((p,ξ),x) ∈ O) (j l : ℕ) :
    ‖angularMixedJet j l (fun p : P × E => fun ν => F ((p.1,ν),p.2)) (p,x) ξ‖ ≤
      ‖iteratedFDeriv ℝ (j+l) F ((p,ξ),x)‖ := by
  obtain ⟨g,hg,_,U,hU,hqU,hUO,he⟩ :=
    exists_contDiff_extension_near_compact hO (isCompact_singleton (x := ((p,ξ),x)))
      (singleton_subset_iff.mpr hq) hF
  let L₁ := ContinuousLinearMap.fst ℝ (P × E) E
  let L₂ := ContinuousLinearMap.snd ℝ (P × E) E
  let L : ((P × E) × E) →L[ℝ] ((P × E) × E) :=
    (((ContinuousLinearMap.fst ℝ P E).comp L₁).prod L₂).prod
      ((ContinuousLinearMap.snd ℝ P E).comp L₁)
  have hL (q : (P × E) × E) : L q = ((q.1.1,q.2),q.1.2) := rfl
  have hLN : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (by
    intro q
    rw [hL,one_mul,Prod.norm_def,Prod.norm_def (x := (q.1.1,q.2))]
    exact max_le (max_le ((norm_fst_le q.1).trans (norm_fst_le q)) (norm_snd_le q))
      ((norm_snd_le q.1).trans (norm_fst_le q)))
  let f (q : P × E) (ν : E) := F ((q.1,ν),q.2)
  let g' (q : P × E) (ν : E) := g ((q.1,ν),q.2)
  have hp : ((p,ξ),x) ∈ U := hqU (mem_singleton _)
  have hEg : g =ᶠ[𝓝 ((p,ξ),x)] F := Filter.mem_of_superset (hU.mem_nhds hp) he
  have hLC : Tendsto L (𝓝 ((p,x),ξ)) (𝓝 ((p,ξ),x)) := L.continuous.continuousAt
  have hComp : Function.uncurry g' =ᶠ[𝓝 ((p,x),ξ)] Function.uncurry f :=
    hEg.comp_tendsto hLC
  change ‖angularMixedJet j l f (p,x) ξ‖ ≤ _
  rw [← angularMixedJet_congr_germ hComp j l,← (hEg.iteratedFDeriv ℝ (j+l)).eq_of_nhds]
  apply (norm_mixedSlice_iteratedFDeriv_le (hg.comp_continuousLinearMap (g := L))
    (p,x) ξ j l).trans
  rw [L.iteratedFDeriv_comp_right hg ((p,x),ξ) (by simp : ((j+l:ℕ):ℕ∞ω) ≤ ∞)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_fin,hL]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hLN)

end CalderonPaper
