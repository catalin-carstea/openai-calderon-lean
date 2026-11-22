module

public import Proof.CalderonN.CompactProductCross
public import Proof.CalderonN.UniformProductCross

import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Tactic

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section
open Set Metric Filter
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open Elliptic.PhaseCoordinates

/-- For a product solution already defined across the interface, its
uniform bound near a strict point is controlled by two compact arms on
the positive side, for every sufficiently close metric in the family. -/
theorem exists_local_bound_of_productPhase
    {g₁ g₂ : ℝ → (MetricField dim)}
    (hg₁ : ∀ a, SmoothMetric univ (g₁ a)) (hg₂ : ∀ a, SmoothMetric univ (g₂ a))
    (hgm₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g₁ q.1 q.2 i j))
    (hgm₂ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g₂ q.1 q.2 i j))
    (ha₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff (g₁ q.1) q.2 i j))
    (ha₂ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff (g₂ q.1) q.2 i j))
    {U : Set ((X dim) × (X dim))} (hU : IsOpen U) (z₀ : (X dim) × (X dim)) (hz₀ : z₀ ∈ U)
    {ρ : (X dim) × (X dim) → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρ₀ : ρ z₀ = 0)
    (hstrict : ProductStrictHessianAt (g₁ 0) (g₂ 0) ρ z₀) :
    ∃ W : Set ((X dim) × (X dim)), IsOpen W ∧ z₀ ∈ W ∧ W ⊆ U ∧
      ∃ K : Set ((X dim) × (X dim)), IsCompact K ∧ K ⊆ {q ∈ U | 0 < ρ q} ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ),
          ∀ (F : (X dim) × (X dim) → ℝ) (M : ℝ), 0 ≤ M →
          ProductSolutionOn (g₁ lam) (g₂ lam) U F →
          (∀ q ∈ K, |F q| ≤ M) → ∀ q ∈ W, |F q| ≤ C*M := by
  obtain ⟨θ₁,θ₂,K,c,r,hθ₁,hθ₂,hθ₁₀,hθ₂₀,_,_,hs₁,hs₂,_,hc,hr,hrU,hgap,hsign⟩ :=
    exists_local_productPhase_gap (hg₁ 0) (hg₂ 0) hU z₀ hz₀ hρ hρ₀ hstrict
  obtain ⟨E₁,hE₁p,hE₁,a₁,k₁,ha₁pos,hk₁,hbig₁,hinterp₁⟩ :=
    exists_family_phaseRoom_interpolation hg₁ hgm₁ ha₁ 0 hθ₁ z₀.1 hθ₁₀ hs₁
  obtain ⟨E₂,hE₂p,hE₂,a₂,k₂,ha₂pos,hk₂,hbig₂,hinterp₂⟩ :=
    exists_family_phaseRoom_interpolation hg₂ hgm₂ ha₂ 0 hθ₂ z₀.2 hθ₂₀ hs₂
  obtain ⟨h₁z,h₁t⟩ := chart_symm_zero E₁ hE₁ (map_zero _) hθ₁₀ hE₁p
  obtain ⟨h₂z,h₂t⟩ := chart_symm_zero E₂ hE₂ (map_zero _) hθ₂₀ hE₂p
  obtain ⟨b₁,hb₁,hbox₁⟩ := exists_box_image_subset_ball E₁ h₁z h₁t hr
  obtain ⟨b₂,hb₂,hbox₂⟩ := exists_box_image_subset_ball E₂ h₂z h₂t hr
  let a := min (min a₁ a₂) (min (b₁/2) (b₂/2))
  let κ := min k₁ k₂
  have ha : 0 < a := lt_min (lt_min ha₁pos ha₂pos) (lt_min (half_pos hb₁) (half_pos hb₂))
  have hab : a ≤ min (b₁/2) (b₂/2) := min_le_right _ _
  have hκ : 0 < κ := lt_min hk₁ hk₂
  have haa₁ : a ≤ a₁ := (min_le_left _ _).trans (min_le_left _ _)
  have haa₂ : a ≤ a₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hba₁ : a < b₁ := (hab.trans (min_le_left _ _)).trans_lt (half_lt_self hb₁)
  have hba₂ : a < b₂ := (hab.trans (min_le_right _ _)).trans_lt (half_lt_self hb₂)
  let R := roomR a
  let l := roomL a c κ
  let ε := roomE a c κ
  have ⟨hR,hRa,_,hl,_,_,_,_,hε,_,hεl,hε4,hcl,hlR,hRa',hκa⟩ := roomParams_spec ha hc hκ
  have hla : l + 4*ε ≤ a := (hlR.trans hRa').le
  have hRa'' : R ≤ a := hRa.trans (by linarith)
  have hsmall₁ : Icc (-a) a ×ˢ closedBall 0 a ⊆ E₁.target :=
    (Set.prod_mono (Icc_subset_Icc (neg_le_neg haa₁) haa₁) (closedBall_subset_closedBall haa₁)).trans hbig₁
  have hsmall₂ : Icc (-a) a ×ˢ closedBall 0 a ⊆ E₂.target :=
    (Set.prod_mono (Icc_subset_Icc (neg_le_neg haa₂) haa₂) (closedBall_subset_closedBall haa₂)).trans hbig₂
  have hlift₁ := hbox₁ a hba₁ hsmall₁
  have hlift₂ := hbox₂ a hba₂ hsmall₂
  let D₁ := E₁.symm '' roomD l ε R
  let D₂ := E₂.symm '' roomD l ε R
  let S₁ := E₁.symm '' (roomStop l ε R ∪ roomSlat l ε R)
  let S₂ := E₂.symm '' (roomStop l ε R ∪ roomSlat l ε R)
  let O₁ := E₁.symm '' roomO l ε R
  let O₂ := E₂.symm '' roomO l ε R
  obtain ⟨hD₁,hS₁D₁,hO₁D₁,hi₁⟩ :=
    hinterp₁ κ l ε R hκ (min_le_left _ _) hε hεl hR (hla.trans haa₁) (hRa''.trans haa₁) hκa hε4
  obtain ⟨hD₂,hS₂D₂,hO₂D₂,hi₂⟩ :=
    hinterp₂ κ l ε R hκ (min_le_right _ _) hε hεl hR (hla.trans haa₂) (hRa''.trans haa₂) hκa hε4
  obtain ⟨_,hO₁,hS₁,_,hT₁,hpc₁,hcD₁,_,_,hcS₁,hsubS₁,_,hTS₁,_,_,_,_,_,_⟩ :=
    native_rooms E₁ hsmall₁ hε hεl hR hla hRa''
  obtain ⟨_,hO₂,hS₂,hT₂o,hT₂,hpc₂,hcD₂,_,_,hcS₂,_,hTO₂,hTS₂,_,_,_,_,_,_⟩ :=
    native_rooms E₂ hsmall₂ hε hεl hR hla hRa''
  have hsd₁ : S₁.Nonempty := hT₁.mono (subset_closure.trans hTS₁)
  have hsd₂ : S₂.Nonempty := hT₂.mono (subset_closure.trans hTS₂)
  have hDbox₁ : closedD l ε R ⊆ E₁.target := (closedD_subset_big hε hla hRa'').trans hsmall₁
  have hDbox₂ : closedD l ε R ⊆ E₂.target := (closedD_subset_big hε hla hRa'').trans hsmall₂
  obtain ⟨_,hDcl₁⟩ := room_closure E₁ roomD_subset_closedD
    (isCompact_Icc.prod (isCompact_closedBall _ _)) hDbox₁
  obtain ⟨_,hDcl₂⟩ := room_closure E₂ roomD_subset_closedD
    (isCompact_Icc.prod (isCompact_closedBall _ _)) hDbox₂
  have hSd {T : Type} [NormedAddCommGroup T] :
      (closedStop l ε R ∪ closedSlat l ε R : Set (ℝ × T)) ⊆ closedD l ε R :=
    (union_subset (closedStop_subset_roomD hε hεl hR) (closedSlat_subset_roomD hε hεl hR)).trans
      roomD_subset_closedD
  obtain ⟨_,hScl₁⟩ := room_closure E₁ (union_subset_union roomStop_subset_closedStop roomSlat_subset_closedSlat)
    ((isCompact_Icc.prod (isCompact_closedBall _ _)).union (isCompact_Icc.prod (isCompact_annulus _ _)))
    (fun _ h => hDbox₁ (hSd h))
  obtain ⟨_,hScl₂⟩ := room_closure E₂ (union_subset_union roomStop_subset_closedStop roomSlat_subset_closedSlat)
    ((isCompact_Icc.prod (isCompact_closedBall _ _)).union (isCompact_Icc.prod (isCompact_annulus _ _)))
    (fun _ h => hDbox₂ (hSd h))
  have hball₁ : E₁.symm '' closedD l ε R ⊆ ball z₀.1 r :=
    (image_mono (closedD_subset_big hε hla hRa'')).trans
      hlift₁
  have hball₂ : E₂.symm '' closedD l ε R ⊆ ball z₀.2 r :=
    (image_mono (closedD_subset_big hε hla hRa'')).trans hlift₂
  have hgapAt (x y : (X dim)) (hx : x ∈ E₁.symm '' closedD l ε R) (hy : y ∈ E₂.symm '' closedD l ε R) :
      (x,y) ∈ closedBall z₀ r := by
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    exact ⟨(mem_ball.mp (hball₁ hx)).le,(mem_ball.mp (hball₂ hy)).le⟩
  let V := {q ∈ U | 0 < ρ q}
  have hArm₁ : closure D₁ ×ˢ closure S₂ ⊆ V := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have h := hgapAt x y (hDcl₁ hx) (image_mono hSd (hScl₂ hy))
    have hgap' := known_cross_gap_two_spaces E₁ E₂ hE₁ hE₂
      (fun v => Submodule.norm_orthogonalProjectionOnto_apply_le _ v) hc hε hR hcl
      hDbox₁ (fun _ h => hDbox₂ (hSd h)) (hDcl₁ hx) (hScl₂ hy) (hgap (x,y) h)
    exact ⟨hrU h,(hsign (x,y) h).mp ((lt_min (half_pos hε) (by positivity)).trans_le hgap')⟩
  have hArm₂ : closure S₁ ×ˢ closure D₂ ⊆ V := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have h := hgapAt x y (image_mono hSd (hScl₁ hx)) (hDcl₂ hy)
    have hgap' := known_cross_gap_two_spaces E₂ E₁ hE₂ hE₁
      (fun v => Submodule.norm_orthogonalProjectionOnto_apply_le _ v) hc hε hR hcl
      hDbox₂ (fun _ h => hDbox₁ (hSd h)) (hDcl₂ hy) (hScl₁ hx)
      (by simpa only [add_comm (θ₂ y), add_comm (‖y-z₀.2‖^2)] using hgap (x,y) h)
    exact ⟨hrU h,(hsign (x,y) h).mp ((lt_min (half_pos hε) (by positivity)).trans_le hgap')⟩
  have hO₁z : z₀.1 ∈ O₁ := by
    refine ⟨(0,0),?_,h₁z⟩
    exact ⟨⟨by linarith,by linarith⟩,mem_ball_self (by positivity)⟩
  have hO₂z : z₀.2 ∈ O₂ := by
    refine ⟨(0,0),?_,h₂z⟩
    exact ⟨⟨by linarith,by linarith⟩,mem_ball_self (by positivity)⟩
  have hroomOD {T : Type} [NormedAddCommGroup T] :
      (roomO l ε R : Set (ℝ × T)) ⊆ closedD l ε R :=
    roomO_subset_closedO.trans ((closedO_subset_roomD hε hεl hR).trans roomD_subset_closedD)
  have hOU : O₁ ×ˢ O₂ ⊆ U := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    exact hrU (hgapAt x y (image_mono hroomOD hx) (image_mono hroomOD hy))
  obtain ⟨r₁,hr₁,hKr₁⟩ := Metric.mem_nhds_iff.mp (hO₁.mem_nhds hO₁z)
  obtain ⟨r₂,hr₂,hKr₂⟩ := Metric.mem_nhds_iff.mp (hO₂.mem_nhds hO₂z)
  let K₁ := closedBall z₀.1 (r₁/2)
  let K₂ := closedBall z₀.2 (r₂/2)
  have hKO₁ : K₁ ⊆ O₁ := (closedBall_subset_ball (half_lt_self hr₁)).trans hKr₁
  have hKO₂ : K₂ ⊆ O₂ := (closedBall_subset_ball (half_lt_self hr₂)).trans hKr₂
  let W := ball z₀.1 (r₁/2) ×ˢ ball z₀.2 (r₂/2)
  let J := closedBall (0 : ℝ) κ
  let K' := (closure D₁ ×ˢ closure S₂) ∪ (closure S₁ ×ˢ closure D₂)
  have hK' : IsCompact K' := (hcD₁.prod hcS₂).union (hcS₁.prod hcD₂)
  obtain ⟨C₁,γ₁,hC₁,hγ₁,_,hI₁⟩ := hi₁
  obtain ⟨C₂,γ₂,hC₂,hγ₂,hγ₂',hI₂⟩ := hi₂
  have hγ : 0 < γ₁+γ₂-1 := by linarith
  have hmetric₁ (a : ℝ) : SmoothMetric D₁ (g₁ a) := smoothMetric_restrict (hg₁ a) (subset_univ D₁)
  have hmetric₂ (a : ℝ) : SmoothMetric D₂ (g₂ a) := smoothMetric_restrict (hg₂ a) (subset_univ D₂)
  have hD₁c : IsConnected D₁ := ⟨hsd₁.mono hS₁D₁,hpc₁⟩
  have hD₂c : IsConnected D₂ := ⟨hsd₂.mono hS₂D₂,hpc₂⟩
  obtain ⟨C,hC,hCross⟩ := exists_uniform_bounded_productCross
    (J := J) (isCompact_closedBall _ _) hD₁ hD₂ hD₁c hD₂c hS₁ hS₂ hsd₁ hsd₂ hO₁ hO₂
    hcS₁ hsubS₁ hS₂D₂ hO₁D₁ hO₂D₂ hcD₁ hcD₂ (isCompact_closedBall _ _) (isCompact_closedBall _ _)
    hKO₁ hKO₂ (fun a _ => hmetric₁ a) (fun a _ => hmetric₂ a)
    (fun i j => (ha₁ i j).contDiffOn) (fun i j => (ha₂ i j).contDiffOn)
    hC₁.le hC₂.le (by linarith) hγ₂'.le hγ
    (fun a ha => hI₁ a (closedBall_subset_closedBall (min_le_left _ _) ha))
    (fun a ha => hI₂ a (closedBall_subset_closedBall (min_le_right _ _) ha))
  have hOc {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (E : OpenPartialHomeomorph (X dim) (ℝ × V)) (hO : roomO l ε R ⊆ E.target) :
      IsPreconnected (E.symm '' roomO l ε R) := by
    have hConv : Convex ℝ (roomO (K := V) l ε R) :=
      (convex_Ioo _ _).prod (convex_ball _ _)
    exact hConv.isPreconnected.image _ (E.continuousOn_symm.mono hO)
  have hO₁c : IsConnected O₁ := ⟨⟨z₀.1,hO₁z⟩,hOc E₁ (hroomOD.trans hDbox₁)⟩
  have hO₂c : IsConnected O₂ := ⟨⟨z₀.2,hO₂z⟩,hOc E₂ (hroomOD.trans hDbox₂)⟩
  refine ⟨W,isOpen_ball.prod isOpen_ball,⟨mem_ball_self (half_pos hr₁),mem_ball_self (half_pos hr₂)⟩,
    (Set.prod_mono (ball_subset_closedBall.trans hKO₁) (ball_subset_closedBall.trans hKO₂)).trans hOU,
    K',hK',union_subset hArm₁ hArm₂,C,hC,?_⟩
  filter_upwards [closedBall_mem_nhds (0 : ℝ) hκ] with lam hlam F M hM hF hData
  obtain ⟨G,hG,hLeft,_,hBnd⟩ := hCross lam hlam F M hM
    (hF.mono ((Set.prod_mono subset_closure subset_closure).trans (hArm₁.trans (fun _ h => h.1))))
    (hF.mono ((Set.prod_mono subset_closure subset_closure).trans (hArm₂.trans (fun _ h => h.1))))
    (fun q hq => hData q (by
      rcases hq with hq | hq
      · exact Or.inl ⟨subset_closure hq.1,subset_closure hq.2⟩
      · exact Or.inr ⟨subset_closure hq.1,subset_closure hq.2⟩))
  have hT2O := subset_closure.trans hTO₂
  have hT2S := subset_closure.trans hTS₂
  have hEq := product_eqOn_of_rectangle hO₁ hO₁c hO₂ hO₂c hO₁ hT₂o hO₁c.1 hT₂
    Subset.rfl hT2O (smoothMetric_restrict (hg₁ lam) (subset_univ O₁))
    (smoothMetric_restrict (hg₂ lam) (subset_univ O₂)) hG (hF.mono hOU)
    (fun q hq => hLeft ⟨hq.1,hT2O hq.2,hT2S hq.2⟩)
  intro q hq
  have hqK : q ∈ K₁ ×ˢ K₂ := ⟨ball_subset_closedBall hq.1,ball_subset_closedBall hq.2⟩
  rw [← hEq ⟨hKO₁ hqK.1,hKO₂ hqK.2⟩]
  exact hBnd q hqK

end CalderonN
