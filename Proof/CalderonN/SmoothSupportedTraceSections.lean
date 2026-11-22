module

public import Proof.CalderonN.SmoothSphereTrace
public import Proof.CalderonN.Coercivity

import Proof.CalderonN.SmoothSphereFields
import Proof.CalderonN.SmoothZonalSobolev
import Mathlib.Tactic

/-! Smooth sphere sections with compact base support. They form a common
domain for the coordinate differential operators and their adjoints. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

abbrev StandardTraceField (dim : ℕ) := X dim × ↥(standardSphere dim) → ℝ

@[expose] def smoothSupportedTraceSections (Y : Set (X dim)) : Submodule ℝ (StandardTraceField dim) where
  carrier := {u | (∃ G : X dim × X dim → ℝ, ContDiff ℝ ∞ G ∧ ∀ x z, u (x,z) = G (x,z)) ∧
    ∃ K : Set (X dim), IsCompact K ∧ K ⊆ Y ∧ ∀ x ∉ K, ∀ z, u (x,z) = 0}
  zero_mem' := ⟨⟨0,contDiff_const,fun _ _ => rfl⟩,
    ⟨∅,isCompact_empty,empty_subset _,fun _ _ _ => rfl⟩⟩
  add_mem' := by
    rintro u v ⟨⟨G,hG,hU⟩,Ku,hKu,hKuY,hu⟩ ⟨⟨H,hH,hV⟩,Kv,hKv,hKvY,hv⟩
    refine ⟨⟨G+H,hG.add hH,?_⟩,Ku ∪ Kv,hKu.union hKv, union_subset hKuY hKvY,?_⟩
    · intro x z
      change u (x,z)+v (x,z) = G (x,z)+H (x,z)
      rw [hU,hV]
    · intro x hx z
      have hxU : x ∉ Ku := fun h => hx (Or.inl h)
      have hxV : x ∉ Kv := fun h => hx (Or.inr h)
      change u (x,z)+v (x,z) = 0
      rw [hu x hxU z,hv x hxV z,add_zero]
  smul_mem' := by
    rintro c u ⟨⟨G,hG,hu⟩,K,hK,hKY,hzero⟩
    refine ⟨⟨c • G,hG.const_smul c,?_⟩,K,hK,hKY,?_⟩
    · intro x z
      change c • u (x,z) = c • G (x,z)
      rw [hu]
    · intro x hx z
      change c • u (x,z) = 0
      rw [hzero x hx z,smul_zero]

abbrev SmoothSupportedTraceSection (Y : Set (X dim)) := ↥(smoothSupportedTraceSections Y)

theorem smoothSupportedTraceSection_repr {Y : Set (X dim)} (u : SmoothSupportedTraceSection Y) :
    ∃ G : X dim × X dim → ℝ, ContDiff ℝ ∞ G ∧ ∀ x z, u.1 (x,z) = G (x,z) := u.2.1

theorem smoothSupportedTraceSection_compact {Y : Set (X dim)} (u : SmoothSupportedTraceSection Y) :
    ∃ K : Set (X dim), IsCompact K ∧ K ⊆ Y ∧ ∀ x ∉ K, ∀ z, u.1 (x,z) = 0 := u.2.2

@[expose] def smoothSupportedTraceFiberL {Y : Set (X dim)} (y : X dim) :
    SmoothSupportedTraceSection Y →ₗ[ℝ] SmoothSphereTrace dim where
  toFun u := ⟨fun z => u.1 (y,z),by
    obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
    let g : smoothBallDataSubmodule dim :=
      ⟨fun z => G (y,z),hG.comp (contDiff_const.prodMk contDiff_id)⟩
    exact ⟨g,funext fun z => (hu y z).symm⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem smoothSupportedTraceFiberL_apply {Y : Set (X dim)} (y : X dim) (u : SmoothSupportedTraceSection Y)
    (z : ↥(standardSphere dim)) : (smoothSupportedTraceFiberL y u).1 z = u.1 (y,z) := rfl

@[expose] def standardTraceBaseDiff (a : X dim) (u : StandardTraceField dim) : StandardTraceField dim :=
  fun p => fderiv ℝ (fun x => u (x,p.2)) p.1 a

theorem standardTraceBaseDiff_of_repr (a : X dim)
    {G : X dim × X dim → ℝ} (hG : ContDiff ℝ ∞ G) {u : StandardTraceField dim}
    (h : ∀ x z, u (x,z) = G (x,z)) (x : X dim) (z : ↥(standardSphere dim)) :
    standardTraceBaseDiff a u (x,z) = fderiv ℝ G (x,z) (a,0) := by
  have hFun : (fun y => u (y,z)) = G ∘ (fun y => (y,(z : X dim))) := funext (fun y => h y z)
  unfold standardTraceBaseDiff
  dsimp only
  rw [hFun,((hG.differentiable (by simp) (x,z)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x (z : X dim))).fderiv]
  rfl

@[expose] def smoothSupportedTraceBaseDiff {Y : Set (X dim)} (a : X dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) where
  toFun u := ⟨standardTraceBaseDiff a u.1,by
    obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
    obtain ⟨K,hK,hKY,hzero⟩ := smoothSupportedTraceSection_compact u
    refine ⟨⟨fun p => fderiv ℝ G p (a,0),
      (hG.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const,
      fun x z => standardTraceBaseDiff_of_repr a hG hu x z⟩,K,hK,hKY,?_⟩
    intro x hx z
    have hz : (fun y => u.1 (y,z)) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact hzero y hy z
    unfold standardTraceBaseDiff
    dsimp only
    rw [hz.fderiv_eq]
    change (fderiv ℝ (fun _ : X dim => (0:ℝ)) x) a = 0
    simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.zero_apply]⟩
  map_add' u v := by
    apply Subtype.ext
    funext ⟨x,z⟩
    obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
    obtain ⟨H,hH,hv⟩ := smoothSupportedTraceSection_repr v
    change standardTraceBaseDiff a (u.1+v.1) (x,z) =
      standardTraceBaseDiff a u.1 (x,z)+standardTraceBaseDiff a v.1 (x,z)
    rw [standardTraceBaseDiff_of_repr a (hG.add hH) (fun x z => by
      change u.1 (x,z)+v.1 (x,z) = G (x,z)+H (x,z)
      rw [hu,hv]),standardTraceBaseDiff_of_repr a hG hu,standardTraceBaseDiff_of_repr a hH hv]
    rw [fderiv_fun_add (hG.differentiable (by simp) _) (hH.differentiable (by simp) _)]
    rfl
  map_smul' := by
    intro c u
    apply Subtype.ext
    funext ⟨x,z⟩
    obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
    change standardTraceBaseDiff a (c • u.1) (x,z) = c • standardTraceBaseDiff a u.1 (x,z)
    rw [standardTraceBaseDiff_of_repr a (hG.const_smul c) (fun x z => by
      change c • u.1 (x,z) = c • G (x,z)
      rw [hu]),standardTraceBaseDiff_of_repr a hG hu,fderiv_fun_const_smul (hG.differentiable (by simp) _) c]
    rfl

theorem smoothSupportedTraceBaseDiff_apply {Y : Set (X dim)} (a : X dim) (u : SmoothSupportedTraceSection Y)
    (x : X dim) (z : ↥(standardSphere dim)) :
    (smoothSupportedTraceBaseDiff a u).1 (x,z) = standardTraceBaseDiff a u.1 (x,z) := rfl

end CalderonN
