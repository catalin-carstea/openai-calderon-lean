module

public import Proof.CalderonN.SmoothSupportedTraceAdjoints
public import Proof.CalderonN.SmoothTraceLinearAdjunction

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! A smooth local fiber operator acts on the same globally supported
space, with pointwise adjunction preserved by the base integral. -/

public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceFiberL_zero_off (u : SmoothSupportedTraceSection Y)
    {x : X dim} (hx : x ∉ Y) : smoothSupportedTraceFiberL x u = 0 := by
  obtain ⟨K,_,hKY,hZero⟩ := smoothSupportedTraceSection_compact u
  apply Subtype.ext
  exact funext (hZero x (fun hxK => hx (hKY hxK)))

/-- There is a smooth angular representative of the action near the unit
sphere. Its values outside this neighborhood play no role. -/
@[expose] def SmoothSupportedTraceFiberRegular (Y : Set (X dim))
    (S : X dim → Module.End ℝ (SmoothSphereTrace dim)) : Prop :=
  ∀ u : SmoothSupportedTraceSection Y, ∃ (U : Set (X dim × X dim)) (F : X dim × X dim → ℝ),
    IsOpen U ∧ Y ×ˢ standardSphere dim ⊆ U ∧ ContDiffOn ℝ ∞ F U ∧
    ∀ x ∈ Y, ∀ z : ↥(standardSphere dim), F (x,z) = (S x (smoothSupportedTraceFiberL x u)).1 z

theorem smoothSupportedTraceFiberAction_mem
    (hY : IsOpen Y) (S : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hS : SmoothSupportedTraceFiberRegular Y S) (u : SmoothSupportedTraceSection Y) :
    (fun q : X dim × ↥(standardSphere dim) => (S q.1 (smoothSupportedTraceFiberL q.1 u)).1 q.2) ∈
      smoothSupportedTraceSections Y := by
  obtain ⟨K,hK,hKY,hZero⟩ := smoothSupportedTraceSection_compact u
  have hZeroL (x : X dim) (hx : x ∉ K) : smoothSupportedTraceFiberL x u = 0 := by
    apply Subtype.ext
    exact funext (hZero x hx)
  obtain ⟨U,F,hU,hYU,hF,hAction⟩ := hS u
  have hSphere : IsCompact (standardSphere dim) := isCompact_sphere _ _
  obtain ⟨W,hW,_,V,hV,hKV,_,hEq⟩ := exists_contDiff_extension_near_compact hU (hK.prod hSphere)
    (fun p hp => hYU ⟨hKY hp.1,hp.2⟩) hF
  obtain ⟨B,T,hB,_,hKB,hST,hBT⟩ := generalized_tube_lemma hK hSphere hV hKV
  obtain ⟨χ,hχ,_,hχS,hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (hB.inter hY) hK.isClosed (subset_inter hKB hKY)
  refine ⟨⟨fun p => χ p.1*W p,(hχ.comp contDiff_fst).mul hW,?_⟩,K,hK,hKY,?_⟩
  · intro x z
    have hVal (hxB : x ∈ B ∩ Y) : W (x,(z : X dim)) = (S x (smoothSupportedTraceFiberL x u)).1 z := by
      have hxz : (x,(z : X dim)) ∈ B ×ˢ T := ⟨hxB.1,hST z.property⟩
      have hW' : W (x,(z : X dim)) = F (x,(z : X dim)) := hEq (hBT hxz)
      exact hW'.trans (hAction x hxB.2 z)
    change (S x (smoothSupportedTraceFiberL x u)).1 z = χ x*W (x,(z : X dim))
    by_cases hx : x ∈ K
    · rw [(hχ1 x).1 hx,one_mul,hVal ⟨hKB hx,hKY hx⟩]
    · rw [hZeroL x hx,map_zero]
      change 0 = χ x*W (x,z)
      by_cases hxB : x ∈ B ∩ Y
      · rw [hVal hxB,hZeroL x hx,map_zero]
        exact (mul_zero _).symm
      · have hχx : χ x = 0 := by
          by_contra h
          have hMem : x ∈ Function.support χ := h
          rw [hχS] at hMem
          exact hxB hMem
        rw [hχx,zero_mul]
  · intro x hx z
    dsimp only
    rw [hZeroL x hx,map_zero]
    rfl

@[expose] def smoothSupportedTraceFiberAction
    (hY : IsOpen Y) (S : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hS : SmoothSupportedTraceFiberRegular Y S) :
    Module.End ℝ (SmoothSupportedTraceSection Y) where
  toFun u := ⟨fun q => (S q.1 (smoothSupportedTraceFiberL q.1 u)).1 q.2,
    smoothSupportedTraceFiberAction_mem hY S hS u⟩
  map_add' u v := by
    apply Subtype.ext
    funext ⟨x,z⟩
    change (S x (smoothSupportedTraceFiberL x (u+v))).1 z =
      (S x (smoothSupportedTraceFiberL x u)).1 z+(S x (smoothSupportedTraceFiberL x v)).1 z
    rw [map_add,map_add]
    rfl
  map_smul' c u := by
    apply Subtype.ext
    funext ⟨x,z⟩
    change (S x (smoothSupportedTraceFiberL x (c • u))).1 z =
      c • (S x (smoothSupportedTraceFiberL x u)).1 z
    rw [map_smul,map_smul]
    rfl

theorem smoothSupportedTraceFiberAction_fiber (hY : IsOpen Y)
    (S : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hS : SmoothSupportedTraceFiberRegular Y S)
    (u : SmoothSupportedTraceSection Y) (x : X dim) :
    smoothSupportedTraceFiberL x (smoothSupportedTraceFiberAction hY S hS u) =
      S x (smoothSupportedTraceFiberL x u) := by
  apply Subtype.ext
  rfl

theorem smoothSupportedTraceFiberAction_adjoint (hn : 3 ≤ dim) (hY : IsOpen Y) (μ : X dim → ℝ)
    (S T : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hS : SmoothSupportedTraceFiberRegular Y S) (hT : SmoothSupportedTraceFiberRegular Y T)
    (hAdj : ∀ x ∈ Y, SmoothTraceAdjoint hn (S x) (T x))
    (u v : SmoothSupportedTraceSection Y) :
    smoothSupportedTracePairing hn μ (smoothSupportedTraceFiberAction hY S hS u) v =
      smoothSupportedTracePairing hn μ u (smoothSupportedTraceFiberAction hY T hT v) := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [smoothSupportedTraceL2,smoothSupportedTraceFiberAction_fiber]
    by_cases hx : x ∈ Y
    · rw [hAdj x hx (smoothSupportedTraceFiberL x u) (smoothSupportedTraceFiberL x v)]
    · simp only [smoothSupportedTraceFiberL_zero_off u hx,smoothSupportedTraceFiberL_zero_off v hx,
        map_zero,inner_zero_left]

theorem smoothSupportedTraceFiberRegular_smul (hY : IsOpen Y) {f : X dim → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) :
    SmoothSupportedTraceFiberRegular Y (fun x => f x • (1 : Module.End ℝ (SmoothSphereTrace dim))) := by
  intro u
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  refine ⟨Prod.fst ⁻¹' Y,fun p => f p.1*G p,hY.preimage continuous_fst,fun _ hp => hp.1,?_,?_⟩
  · exact (hf.comp contDiff_fst.contDiffOn (fun _ h => h)).mul hG.contDiffOn
  · intro x _ z
    change f x * G (x,z) = f x * u.1 (x,z)
    rw [hu]

end CalderonN
