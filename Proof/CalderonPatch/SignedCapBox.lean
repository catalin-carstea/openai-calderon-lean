module

public import Proof.CalderonPatch.NativeNormalChart

import Mathlib.Tactic

public section
noncomputable section
open Metric Set
open scoped Topology

namespace CalderonPatch

open CalderonN (I X)

variable {n : ℕ} [NeZero n]
local notation "L" => (inwardChartSplit (n := n))
local notation "Z" => boundaryTangentPlane (0 : I n)

/-- A signed coordinate box containing the complete support of the
vertical push, strictly inside its faces. -/
structure SignedCapBox (W : Set (Z × ℝ)) (z : Z) where
  lower : I n → ℝ
  upper : I n → ℝ
  bounds : lower ≤ upper
  radius : ℝ
  radius_pos : 0 < radius
  bottom_lt : lower 0 < -radius
  top_lt : radius < upper 0
  box_inside : MapsTo (L ∘ WithLp.toLp 2) (Icc lower upper) W
  push_inside : MapsTo (WithLp.ofLp ∘ (inwardChartSplit (n := n)).symm)
    (closedBall z radius ×ˢ Icc (-radius) radius)
    (Set.pi univ fun i => Ioo (lower i) (upper i))

theorem SignedCapBox.support_inside {W : Set (Z × ℝ)} {z : Z}
    (B : SignedCapBox W z) : closedBall z B.radius ×ˢ Icc (-B.radius) B.radius ⊆ W := by
  intro p hp
  have h := Set.mem_pi.mp (B.push_inside hp)
  have hpBox : WithLp.ofLp ((inwardChartSplit (n := n)).symm p) ∈ Icc B.lower B.upper :=
    ⟨fun i => (h i (mem_univ i)).1.le,fun i => (h i (mem_univ i)).2.le⟩
  have hpW := B.box_inside hpBox
  rw [Function.comp_apply,WithLp.toLp_ofLp,(inwardChartSplit (n := n)).apply_symm_apply] at hpW
  exact hpW

theorem exists_signedCapBox {W : Set (Z × ℝ)} (hW : IsOpen W) {z : Z}
    (hz : (z,(0 : ℝ)) ∈ W) : Nonempty (SignedCapBox W z) := by
  let c := (inwardChartSplit (n := n)).symm (z,0)
  have hc : c 0 = 0 := by
    rw [← inwardChartSplit_height,(inwardChartSplit (n := n)).apply_symm_apply]
  let mapToProduct : (I n → ℝ) → Z × ℝ := L ∘ WithLp.toLp 2
  let U := mapToProduct ⁻¹' W
  have hMap : Continuous mapToProduct := (inwardChartSplit (n := n)).continuous.comp
    (PiLp.continuous_toLp 2 (fun _ : I n => ℝ))
  have hU : IsOpen U := hW.preimage hMap
  have hcU : WithLp.ofLp c ∈ U := by
    change L (WithLp.toLp 2 (WithLp.ofLp c)) ∈ W
    rwa [WithLp.toLp_ofLp,(inwardChartSplit (n := n)).apply_symm_apply]
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hcU)
  let a (i : I n) := c i - δ / 2
  let b (i : I n) := c i + δ / 2
  have hab : a ≤ b := fun i => by dsimp only [a,b]; linarith
  have hBox : MapsTo mapToProduct (Icc a b) W := by
    intro y hy
    apply hδU
    rw [mem_ball,dist_pi_lt_iff hδ]
    intro i
    rw [Real.dist_eq,abs_lt]
    have ha := hy.1 i
    have hb := hy.2 i
    dsimp only [a,b] at ha hb
    change -δ < y i - c i ∧ y i - c i < δ
    constructor <;> linarith
  let mapFromProduct : Z × ℝ → (I n → ℝ) := WithLp.ofLp ∘ (inwardChartSplit (n := n)).symm
  let V := mapFromProduct ⁻¹' (Set.pi univ fun i => Ioo (a i) (b i))
  have hInv : Continuous mapFromProduct := (PiLp.continuous_ofLp 2 (fun _ : I n => ℝ)).comp
    (inwardChartSplit (n := n)).symm.continuous
  have hV : IsOpen V := (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage hInv
  have hzV : (z,(0 : ℝ)) ∈ V := by
    change WithLp.ofLp c ∈ Set.pi univ (fun i => Ioo (a i) (b i))
    rw [Set.mem_pi]
    intro i _
    change c i - δ/2 < c i ∧ c i < c i + δ/2
    constructor <;> linarith
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  let r := min (ε/2) (δ/4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r ≤ δ/4 := min_le_right _ _
  have hrε : r < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨⟨a,b,hab,r,hr,?_,?_,hBox,?_⟩⟩
  · change c 0 - δ/2 < -r
    rw [hc]
    linarith
  · change r < c 0 + δ/2
    rw [hc]
    linarith
  · intro p hp
    apply hεV
    rw [mem_ball,Prod.dist_eq]
    have h₁ : dist p.1 z ≤ r := mem_closedBall.mp hp.1
    have h₂ : dist p.2 (0 : ℝ) ≤ r := by
      rw [Real.dist_eq,sub_zero,abs_le]
      exact hp.2
    exact max_lt (h₁.trans_lt hrε) (h₂.trans_lt hrε)

end CalderonPatch
