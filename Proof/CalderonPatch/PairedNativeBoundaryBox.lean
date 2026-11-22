module

public import Proof.CalderonPatch.CommonBoundaryCoordinates
public import Proof.CalderonPatch.BoundaryChartTests

import Mathlib.Tactic

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ}
local notation "E" => X (n+1)
local notation "Y" => X n
local notation "J" => 𝓡∂ (n+1)
local notation "L" => (inwardChartSplit (n := n+1))
local notation "P" => boundaryTangentPlane (0 : I (n+1)) × ℝ

/-- Choose a closed coordinate half box around a flat-face point
inside a prescribed open signed neighborhood. -/
theorem exists_boundaryHalfBox_inside {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    (hx0 : x 0 = 0) :
    ∃ l r : I (n+1) → ℝ, l ≤ r ∧ l 0 = 0 ∧ 0 < r 0 ∧
      normalTangentialCoordinates x ∈ tangentialBox l r ∧
      MapsTo (WithLp.toLp 2) (Icc l r) O := by
  let V : Set (I (n+1) → ℝ) := (WithLp.toLp 2) ⁻¹' O
  have hV : IsOpen V := hO.preimage (PiLp.continuous_toLp 2 (fun _ : I (n+1) => ℝ))
  have hxV : WithLp.ofLp x ∈ V := by
    change WithLp.toLp 2 (WithLp.ofLp x) ∈ O
    rwa [WithLp.toLp_ofLp]
  obtain ⟨ε,hε,hBall⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  let l (i : I (n+1)) := if i = 0 then 0 else x i - ε/2
  let r (i : I (n+1)) := x i + ε/2
  have hl0 : l 0 = 0 := by simp [l]
  have hr0 : 0 < r 0 := by simpa only [r,hx0,zero_add] using half_pos hε
  have hlr : l ≤ r := by
    intro i
    by_cases h : i = 0
    · subst i
      simpa only [hl0] using hr0.le
    · dsimp only [l,r]
      rw [ite_eq_right h]
      linarith
  refine ⟨l,r,hlr,hl0,hr0,?_,?_⟩
  · intro i
    simp only [normalTangentialCoordinates,WithLp.ofLp_toLp,l,r,
      ite_eq_right (Fin.succAbove_ne _ _)]
    constructor <;> linarith
  · intro z hz
    apply hBall
    rw [mem_ball,dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq,abs_lt]
    have hu := hz.2 i
    have hd := hz.1 i
    dsimp only [r] at hu
    by_cases h : i = 0
    · subst i
      rw [hl0] at hd
      change x 0 = 0 at hx0
      change -ε < z 0 - x 0 ∧ z 0 - x 0 < ε
      constructor <;> linarith
    · simp only [l,ite_eq_right h] at hd
      change -ε < z i - x i ∧ z i - x i < ε
      constructor <;> linarith

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

/-- The normal charts for the two metrics, with the product charts
used for cap attachment and one common coordinate half box used for
the measured boundary jets. -/
structure PairedNativeBoundaryBox (g₁ g₂ : SmoothMetric (n+1) M)
    (Γ : Set ((J).boundary M)) (p : (J).boundary M) where
  prod₁ : ProductBoundaryChart (n := n+1) (M := M) (Z := boundaryTangentPlane (0 : I (n+1)))
  prod₂ : ProductBoundaryChart (n := n+1) (M := M) (Z := boundaryTangentPlane (0 : I (n+1)))
  first : NativeBoundaryMetricChart g₁ p
  second : NativeBoundaryMetricChart g₂ p
  source₁ : first.coord.source = prod₁.coord.source
  source₂ : second.coord.source = prod₂.coord.source
  ambient₁ : first.ambient = L ⁻¹' prod₁.ambient
  ambient₂ : second.ambient = L ⁻¹' prod₂.ambient
  coord₁ : (first.coord : M → E) = (inwardChartSplit (n := n+1)).symm ∘ prod₁.coord
  coord₂ : (second.coord : M → E) = (inwardChartSplit (n := n+1)).symm ∘ prod₂.coord
  signed : Set E
  open_signed : IsOpen signed
  signed₁ : signed ⊆ first.ambient
  signed₂ : signed ⊆ second.ambient
  center_signed : second.coord p ∈ signed
  trace_first : ∀ q : (J).boundary M, (q : M) ∈ first.coord.source → first.coord q ∈ signed → q ∈ Γ
  trace_second : ∀ q : (J).boundary M, (q : M) ∈ second.coord.source → second.coord q ∈ signed →
    (q : M) ∈ first.coord.source ∧ first.coord q = second.coord q ∧ q ∈ Γ
  common_inverse : EqOn first.coord.symm second.coord.symm (signed ∩ {z | z 0 = 0})
  boxLower : I (n+1) → ℝ
  boxUpper : I (n+1) → ℝ
  bounds : boxLower ≤ boxUpper
  lower_zero : boxLower 0 = 0
  upper_pos : 0 < boxUpper 0
  center_box : normalTangentialCoordinates (second.coord p) ∈ tangentialBox boxLower boxUpper
  closed_box : MapsTo (WithLp.toLp 2) (Icc boxLower boxUpper) signed
  face_patch : MapsTo (first.coord.symm ∘ normalFacePoint) (tangentialBox boxLower boxUpper) (Subtype.val '' Γ)

set_option maxHeartbeats 1000000 in
/-- At any point of the measured patch the two inward normal charts
have the same coordinates on the original boundary and a common
smaller half box contained in the patch. -/
theorem exists_pairedNativeBoundaryBox (g₁ g₂ : SmoothMetric (n+1) M)
    {Γ : Set ((J).boundary M)} (hΓ : IsOpen Γ) {p : (J).boundary M} (hp : p ∈ Γ) :
    Nonempty (PairedNativeBoundaryBox g₁ g₂ Γ p) := by
  obtain ⟨D₁,e₁,A₁,hp₁,_,_,hS₁,hB₁,hC₁,hA₁,hAmb₁,hAp₁,hAi₁⟩ :=
    exists_nativeBoundaryMetricChart_with_product g₁ p p.property
  obtain ⟨D₂,e₂,A₂,hp₂,_,_,hS₂,hB₂,hC₂,hA₂,hAmb₂,hAp₂,hAi₂⟩ :=
    exists_nativeBoundaryMetricChart_with_product g₂ p p.property
  have hSame (q : (J).boundary M) (hq₁ : (q : M) ∈ D₁.coord.source)
      (hq₂ : (q : M) ∈ D₂.coord.source) : D₁.coord q = D₂.coord q :=
    (normalChart_eq_original_on_boundary (p : M) D₁ e₁ hS₁ hB₁ hC₁ q.property hq₁).trans
      (normalChart_eq_original_on_boundary (p : M) D₂ e₂ hS₂ hB₂ hC₂ q.property hq₂).symm
  obtain ⟨W,hW,hpW,hW₁,hW₂,hTrace₁,hTrace₂⟩ :=
    exists_pairedBoundaryNeighborhood D₁ D₂ hp₁ hp₂ hΓ hp hSame
  let O := L ⁻¹' W
  have hO : IsOpen O := hW.preimage (inwardChartSplit (n := n+1)).continuous
  have hO₁ : O ⊆ A₁.ambient := by rw [hAmb₁]; exact preimage_mono hW₁
  have hO₂ : O ⊆ A₂.ambient := by rw [hAmb₂]; exact preimage_mono hW₂
  have hMem₁ (q : M) : A₁.coord q ∈ O ↔ D₁.coord q ∈ W := by
    change L (A₁.coord q) ∈ W ↔ _
    rw [congrFun hAp₁ q,Function.comp_apply,(inwardChartSplit (n := n+1)).apply_symm_apply]
  have hMem₂ (q : M) : A₂.coord q ∈ O ↔ D₂.coord q ∈ W := by
    change L (A₂.coord q) ∈ W ↔ _
    rw [congrFun hAp₂ q,Function.comp_apply,(inwardChartSplit (n := n+1)).apply_symm_apply]
  have hpO : A₂.coord p ∈ O := (hMem₂ p).mpr hpW
  have hTrace₁' (q : (J).boundary M) (hq : (q : M) ∈ A₁.coord.source)
      (ho : A₁.coord q ∈ O) : q ∈ Γ := hTrace₁ q (hA₁ ▸ hq) ((hMem₁ q).mp ho)
  have hTrace₂' (q : (J).boundary M) (hq : (q : M) ∈ A₂.coord.source)
      (ho : A₂.coord q ∈ O) :
      (q : M) ∈ A₁.coord.source ∧ A₁.coord q = A₂.coord q ∧ q ∈ Γ := by
    obtain ⟨h1,h2,h3⟩ := hTrace₂ q (hA₂ ▸ hq) ((hMem₂ q).mp ho)
    exact ⟨hA₁.symm ▸ h1,by simp only [congrFun hAp₁ q,congrFun hAp₂ q,Function.comp_apply,h2],h3⟩
  have hFace (x : E) (hx : x ∈ O ∩ {x | x 0 = 0}) :
      ∃ q : (J).boundary M, (q : M) = A₂.coord.symm x ∧
        A₁.coord.symm x = q ∧ q ∈ Γ := by
    have hx0 : x 0 = 0 := hx.2
    have hxT : x ∈ A₂.coord.target :=
      A₂.target_eq.symm ▸ ⟨hO₂ hx.1,(mem_inwardHalfSpace).mpr hx0.ge⟩
    let q := A₂.coord.symm x
    have hqS : q ∈ A₂.coord.source := A₂.coord.map_target hxT
    have hqX : A₂.coord q = x := A₂.coord.right_inv hxT
    have hqBd : q ∈ (J).boundary M := by
      rw [← (J).compl_interior,mem_compl_iff,A₂.interior_iff q hqS,hqX,mem_positiveHalfSpace,hx0]
      exact lt_irrefl _
    obtain ⟨hq₁,hqEq,hqΓ⟩ := hTrace₂' ⟨q,hqBd⟩ hqS (hqX.symm ▸ hx.1)
    refine ⟨⟨q,hqBd⟩,rfl,?_,hqΓ⟩
    change A₁.coord.symm x = q
    rw [← hqX,← hqEq,A₁.coord.left_inv hq₁]
  obtain ⟨l,r,hlr,hl0,hr,hCenter,hBox⟩ := exists_boundaryHalfBox_inside hO hpO A₂.point_face
  have hΓ' : MapsTo (A₁.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ) := by
    intro y hy
    have hXb : WithLp.ofLp (normalFacePoint y) ∈ Icc l r :=
      normalHalfBox_subset_closedBox hl0 (by
        refine ⟨(normalFacePoint_height y).ge,?_,?_⟩
        · intro j
          by_cases hj : j = 0
          · subst j; rwa [normalFacePoint_height]
          · obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq hj
            exact (hy i).2
        · intro j hj
          obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq hj
          exact (hy i).1)
    have hX := hBox hXb
    rw [WithLp.toLp_ofLp] at hX
    obtain ⟨q,_,hqX,hqΓ⟩ := hFace (normalFacePoint y) ⟨hX,normalFacePoint_height y⟩
    exact ⟨q,hqΓ,hqX.symm⟩
  refine ⟨⟨D₁,D₂,A₁,A₂,hA₁,hA₂,hAmb₁,hAmb₂,hAp₁,hAp₂,O,hO,hO₁,hO₂,hpO,
    hTrace₁',hTrace₂',?_,l,r,hlr,hl0,hr,hCenter,hBox,hΓ'⟩⟩
  intro x hx
  obtain ⟨q,he,hq,_⟩ := hFace x hx
  exact hq.trans he

end CalderonPatch
