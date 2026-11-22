module

public import Proof.CalderonN.MixedSliceJets
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper.LowerGreen

variable {X P Q F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem exists_contDiff_germ_extension {f : P → F} {p : P} {k : ℕ}
    [FiniteDimensional ℝ P] {S : Set P} (hS : IsOpen S) (hSp : p ∈ S)
    (hfS : ContDiffOn ℝ k f S) :
    ∃ g : P → F, ContDiff ℝ k g ∧ g =ᶠ[𝓝 p] f := by
  obtain ⟨a,ha,haS⟩ := Metric.isOpen_iff.mp hS p hSp
  let b : ContDiffBump p := ⟨a/4,a/2,by positivity,by linarith⟩
  let g (x : P) := (b x) • f x
  refine ⟨g,contDiff_iff_contDiffAt.mpr fun x => ?_,?_⟩
  · by_cases hx : x ∈ S
    · have hb : ContDiff ℝ k (b : P → ℝ) := b.contDiff
      exact hb.contDiffAt.smul (hfS.contDiffAt (hS.mem_nhds hx))
    · have hOut : x ∉ tsupport (b : P → ℝ) := by
        intro hxB
        apply hx
        refine haS (closedBall_subset_ball (show a/2 < a by linarith) ?_)
        rwa [b.tsupport_eq] at hxB
      have h0 : (b : P → ℝ) =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hOut
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [h0] with z hz
      simp only [g,hz,zero_smul]
  · have hB : ball p (a/4) ∈ 𝓝 p := ball_mem_nhds p (by positivity)
    filter_upwards [hB] with z hz
    have hb : b z = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hz)
    simp only [g,hb,one_smul]

private theorem slice_norm_le_of_contDiffAt
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    {f : P × Q → F} (p : P) (w : Q) (k : ℕ) {S : Set (P × Q)}
    (hS : IsOpen S) (hP : (p,w) ∈ S) (hf : ContDiffOn ℝ k f S) :
    ‖iteratedFDeriv ℝ k (fun z => f (p,z)) w‖ ≤ ‖iteratedFDeriv ℝ k f (p,w)‖ := by
  obtain ⟨g,hg,he⟩ := exists_contDiff_germ_extension hS hP hf
  have hSlice : (fun z => g (p,z)) =ᶠ[𝓝 w] (fun z => f (p,z)) := he.comp_tendsto ((continuous_const.prodMk continuous_id).continuousAt.tendsto :
    Tendsto (fun z : Q => (p,z)) (𝓝 w) (𝓝 (p,w)))
  rw [← (hSlice.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,← (he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  let L := ContinuousLinearMap.inr ℝ P Q
  let b : P × Q := (p,0)
  let A (x : P × Q) := g (x+b)
  have hA : ContDiff ℝ k A := hg.comp (contDiff_id.add contDiff_const)
  have h := L.iteratedFDeriv_comp_right hA w (i := k) (by simp)
  rw [show iteratedFDeriv ℝ k A (L w) = iteratedFDeriv ℝ k g (p,w) by
    simpa only [A,L,b,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero] using
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := g) k b (L w)] at h
  have hEq : iteratedFDeriv ℝ k (fun z => g (p,z)) w =
      (iteratedFDeriv ℝ k g (p,w)).compContinuousLinearMap (fun _ => L) := by
    simpa only [Function.comp_def,A,L,b,ContinuousLinearMap.inr_apply,Prod.mk_add_mk,zero_add,add_zero] using h
  rw [hEq]
  exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _ (fun _ => LinearIsometry.inr ℝ P Q)

set_option maxHeartbeats 2000000 in
/-- A finite smooth model on an open room around a fixed parameter-angular
compact set bounds both angular jets and one true base derivative. -/
theorem exists_uniform_baseComposed_mixed_jets
    [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    {T K : Set (P × Q)} (hT : IsOpen T) (hK : IsCompact K) (hKT : K ⊆ T)
    {f : P × Q → ℝ} {k : ℕ} (hf : ContDiffOn ℝ (k+1 : ℕ) f T)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : X → P, ContDiff ℝ ∞ a → ∀ y w, (a y,w) ∈ K →
      ‖fderiv ℝ a y‖ ≤ D →
      ‖iteratedFDeriv ℝ k (fun z => f (a y,z)) w‖ ≤ C ∧
      ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => f (a x,z)) y) w‖ ≤ C := by
  let U (q : P × Q) := (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ P Q)
  have hU : ContDiffOn ℝ k U T :=
    (hf.fderiv_of_isOpen (m := (k : ℕ)) hT (by norm_cast)).clm_comp contDiffOn_const
  have hfK : ContinuousOn (fun q => ‖iteratedFDeriv ℝ k f q‖) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv hf hT (show (k : ℕ∞ω) ≤ (↑(k+1) : ℕ∞ω)
      by norm_cast; omega)).norm.mono hKT
  have hUK : ContinuousOn (fun q => ‖iteratedFDeriv ℝ k U q‖) K :=
    (ContinuousOn.continuousOn_iteratedFDeriv hU hT le_rfl).norm.mono hKT
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hfK
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hUK
  let C := max (max 0 B) ((max 0 A) * D)
  refine ⟨C,(le_max_left _ _).trans (le_max_left _ _),?_⟩
  intro a ha y w hp haD
  have hpT := hKT hp
  have hff : ContDiffOn ℝ k f T := hf.of_le (by norm_cast; omega)
  have hNormF : ‖iteratedFDeriv ℝ k f (a y,w)‖ ≤ max 0 B :=
    (le_abs_self _).trans ((hB (a y,w) hp).trans (le_max_right _ _))
  refine ⟨(slice_norm_le_of_contDiffAt (a y) w k hT hpT hff).trans (hNormF.trans (le_max_left _ _)),?_⟩
  let E := fderiv ℝ a y
  let L : (P →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ X P ℝ).flip E
  have hGerm : (fun z => fderiv ℝ (fun x => f (a x,z)) y) =ᶠ[𝓝 w]
      fun z => L (U (a y,z)) := by
    have hN := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hT.mem_nhds hpT)
    filter_upwards [hN] with z hz
    have hM := ((ha.differentiable (by simp) y).hasFDerivAt.prodMk
      (hasFDerivAt_const (𝕜 := ℝ) z y))
    have hD₀ : DifferentiableAt ℝ f (a y,z) :=
      (hf.contDiffAt (hT.mem_nhds hz)).differentiableAt (by norm_cast)
    change fderiv ℝ (f ∘ fun x => (a x,z)) y = _
    rw [(hD₀.hasFDerivAt.comp y hM).fderiv]
    ext v
    rfl
  have hUi : ContDiffAt ℝ k U (a y,w) := hU.contDiffAt (hT.mem_nhds hpT)
  have hUs : ContDiffAt ℝ k (fun z => U (a y,z)) w :=
    hUi.comp w (contDiff_const.prodMk contDiff_id).contDiffAt
  rw [(hGerm.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  change ‖iteratedFDeriv ℝ k (L ∘ fun z => U (a y,z)) w‖ ≤ _
  rw [L.iteratedFDeriv_comp_left hUs le_rfl]
  have hL : ‖L‖ ≤ D := by
    apply ContinuousLinearMap.opNorm_le_bound _ hD
    intro v
    exact (ContinuousLinearMap.opNorm_comp_le v E).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left haD (norm_nonneg v))
  have hNormU : ‖iteratedFDeriv ℝ k U (a y,w)‖ ≤ max 0 A :=
    (le_abs_self _).trans ((hA (a y,w) hp).trans (le_max_right _ _))
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    ((mul_le_mul hL ((slice_norm_le_of_contDiffAt (a y) w k hT hpT hU).trans hNormU)
        (norm_nonneg _) hD).trans
      (by rw [mul_comm]; exact le_max_right _ _))

end CalderonPaper.LowerGreen

end
