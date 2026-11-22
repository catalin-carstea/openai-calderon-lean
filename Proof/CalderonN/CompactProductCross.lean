module

public import Proof.CalderonN.PhaseRoomInterpolation
public import Proof.CalderonN.LocalProductPhaseGap
public import Proof.CalderonN.HarmonicTaylorApproximation
public import Proof.CalderonN.StrongCrossExtension
public import Proof.CalderonN.PhaseVertical

import Proof.CalderonN.ClassicalInteriorJets
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

open Elliptic.PhaseCoordinates

theorem product_memLp_of_compact_buffer {A B : Set (X dim)}
    (hA : IsOpen A) (hB : IsOpen B) {K : Set ((X dim) × (X dim))} (hK : IsCompact K)
    (hle : A ×ˢ B ⊆ K) {F : (X dim) × (X dim) → ℝ} (hF : ContinuousOn F K) :
    MemLp F 2 (((volume : Measure (X dim)).restrict A).prod ((volume : Measure (X dim)).restrict B)) := by
  rw [Measure.prod_restrict]
  have hmeas := (hF.mono hle).aestronglyMeasurable (hA.prod hB).measurableSet
    (μ := (volume : Measure (X dim)).prod volume)
  exact (memLp_two_iff_integrable_sq hmeas).mpr ((hF.pow 2).integrableOn_compact hK |>.mono_set hle)

/-- The exact source product Hessian test supplies a product solution
from two compactly contained input arms above the reference level.
Both of the open intersections with the output rectangle agree pointwise. -/
theorem exists_compact_productCross_extension
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {U : Set ((X dim) × (X dim))} (hU : IsOpen U) (z₀ : (X dim) × (X dim)) (hz₀ : z₀ ∈ U)
    {ρ : (X dim) × (X dim) → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρ₀ : ρ z₀ = 0)
    (hstrict : ProductStrictHessianAt g₁ g₂ ρ z₀) {F : (X dim) × (X dim) → ℝ}
    (hF : ProductSolutionOn g₁ g₂ {q ∈ U | 0 < ρ q} F) :
    ∃ D₁ D₂ S₁ S₂ O₁ O₂ : Set (X dim),
      IsOpen O₁ ∧ IsOpen O₂ ∧ z₀ ∈ O₁ ×ˢ O₂ ∧
      IsCompact (closure D₁) ∧ IsCompact (closure D₂) ∧
      IsCompact (closure S₁) ∧ IsCompact (closure S₂) ∧
      (closure D₁ ×ˢ closure S₂) ∪ (closure S₁ ×ˢ closure D₂) ⊆ {q ∈ U | 0 < ρ q} ∧
      ∃ G, ProductSolutionOn g₁ g₂ (O₁ ×ˢ O₂) G ∧
        EqOn G F ((O₁ ×ˢ O₂) ∩ {q ∈ U | 0 < ρ q}) := by
  obtain ⟨θ₁,θ₂,K,c,r,hθ₁,hθ₂,hθ₁₀,hθ₂₀,_,hjet₂,hs₁,hs₂,_,hc,hr,hrU,hgap,hsign⟩ :=
    exists_local_productPhase_gap hg₁ hg₂ hU z₀ hz₀ hρ hρ₀ hstrict
  obtain ⟨E₁,hE₁p,hE₁,a₁,k₁,ha₁,hk₁,hbig₁,hinterp₁⟩ :=
    exists_phaseRoom_interpolation hg₁ hθ₁ z₀.1 hθ₁₀ hs₁
  obtain ⟨E₂,hE₂p,hE₂,a₂,k₂,ha₂,hk₂,hbig₂,hinterp₂⟩ :=
    exists_phaseRoom_interpolation hg₂ hθ₂ z₀.2 hθ₂₀ hs₂
  obtain ⟨h₁z,h₁t⟩ := chart_symm_zero E₁ hE₁ (map_zero _) hθ₁₀ hE₁p
  obtain ⟨h₂z,h₂t⟩ := chart_symm_zero E₂ hE₂ (map_zero _) hθ₂₀ hE₂p
  have hℓ₂ : fderiv ℝ θ₂ z₀.2 ≠ 0 := fun h => hs₂.1 (funext fun i => by simp [coordDeriv,h])
  obtain ⟨d,hd,hheight⟩ := exists_monotone_second_height hU z₀ hz₀ hρ hθ₂ hθ₂₀ hℓ₂ hjet₂ E₂ hE₂p hE₂
  obtain ⟨b₁,hb₁,hbox₁⟩ := exists_box_image_subset_ball E₁ h₁z h₁t (lt_min hr hd)
  obtain ⟨b₂,hb₂,hbox₂⟩ := exists_box_image_subset_ball E₂ h₂z h₂t hr
  let a := min (min a₁ a₂) (min (min (b₁/2) (b₂/2)) (d/2))
  let κ := min k₁ k₂
  have ha : 0 < a := lt_min (lt_min ha₁ ha₂) (lt_min (lt_min (half_pos hb₁) (half_pos hb₂)) (half_pos hd))
  have had : a < d := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hd)
  have hab : a ≤ min (b₁/2) (b₂/2) := (min_le_right _ _).trans (min_le_left _ _)
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
    (prod_mono (Icc_subset_Icc (neg_le_neg haa₁) haa₁) (closedBall_subset_closedBall haa₁)).trans hbig₁
  have hsmall₂ : Icc (-a) a ×ˢ closedBall 0 a ⊆ E₂.target :=
    (prod_mono (Icc_subset_Icc (neg_le_neg haa₂) haa₂) (closedBall_subset_closedBall haa₂)).trans hbig₂
  have hlift₁ := hbox₁ a hba₁ hsmall₁
  have hlift₂ := hbox₂ a hba₂ hsmall₂
  let D₁ := E₁.symm '' roomD l ε R
  let D₂ := E₂.symm '' roomD l ε R
  let S₁ := E₁.symm '' (roomStop l ε R ∪ roomSlat l ε R)
  let S₂ := E₂.symm '' (roomStop l ε R ∪ roomSlat l ε R)
  let O₁ := E₁.symm '' roomO l ε R
  let O₂ := E₂.symm '' roomO l ε R
  obtain ⟨hD₁,hgD₁,hS₁D₁,hO₁D₁,hi₁⟩ :=
    hinterp₁ κ l ε R hκ (min_le_left _ _) hε hεl hR (hla.trans haa₁) (hRa''.trans haa₁) hκa hε4
  obtain ⟨hD₂,hgD₂,hS₂D₂,hO₂D₂,hi₂⟩ :=
    hinterp₂ κ l ε R hκ (min_le_right _ _) hε hεl hR (hla.trans haa₂) (hRa''.trans haa₂) hκa hε4
  obtain ⟨_,hO₁,hS₁,_,hT₁,hpc₁,hcD₁,_,_,hcS₁,hsubS₁,_,hTS₁,_,_,_,_,_,_⟩ :=
    native_rooms E₁ hsmall₁ hε hεl hR hla hRa''
  obtain ⟨_,hO₂,hS₂,_,hT₂,hpc₂,hcD₂,_,_,hcS₂,hsubS₂,_,hTS₂,_,_,_,_,_,_⟩ :=
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
      (hlift₁.trans (ball_subset_ball (min_le_left _ _)))
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
  refine ⟨D₁,D₂,S₁,S₂,O₁,O₂,hO₁,hO₂,⟨hO₁z,hO₂z⟩,hcD₁,hcD₂,hcS₁,hcS₂,
    union_subset hArm₁ hArm₂,?_⟩
  obtain ⟨C₁,γ₁,hC₁,hγ₁,_,hinter₁⟩ := hi₁
  obtain ⟨C₂,γ₂,hC₂,hγ₂,hγ₂',hinter₂⟩ := hi₂
  have hγ : 0 < γ₁+γ₂-1 := by linarith
  have hM₁ := product_memLp_of_compact_buffer hD₁ hS₂ (hcD₁.prod hcS₂)
    (prod_mono subset_closure subset_closure) (hF.1.continuousOn.mono hArm₁)
  have hM₂ := product_memLp_of_compact_buffer hS₁ hD₂ (hcS₁.prod hcD₂)
    (prod_mono subset_closure subset_closure) (hF.1.continuousOn.mono hArm₂)
  obtain ⟨G,hG,hLeft,hRight⟩ := exists_productSolutionOn_cross_of_interpolation hD₁ hD₂
    ⟨hsd₁.mono hS₁D₁,hpc₁⟩ ⟨hsd₂.mono hS₂D₂,hpc₂⟩ hS₁ hS₂ hsd₁ hsd₂ hO₁ hO₂
    hO₁D₁ hO₂D₂ hcS₁ hsubS₁ hS₂D₂ hgD₁ hgD₂
    ((measure_mono subset_closure).trans_lt hcD₂.measure_lt_top).ne
    hC₁.le hC₂.le (by linarith) hγ₂'.le hγ hinter₁ hinter₂ hM₁ hM₂
    (hF.mono ((prod_mono subset_closure subset_closure).trans hArm₁))
    (hF.mono ((prod_mono subset_closure subset_closure).trans hArm₂))
  refine ⟨G,hG,?_⟩
  have hroomOD {T : Type} [NormedAddCommGroup T] :
      (roomO l ε R : Set (ℝ × T)) ⊆ closedD l ε R :=
    roomO_subset_closedO.trans ((closedO_subset_roomD hε hεl hR).trans roomD_subset_closedD)
  have hOtarget := hroomOD.trans hDbox₂
  have hO₁d : O₁ ⊆ ball z₀.1 d :=
    (image_mono (hroomOD.trans (closedD_subset_big hε hla hRa''))).trans
      (hlift₁.trans (ball_subset_ball (min_le_right _ _)))
  have hOU : O₁ ×ˢ O₂ ⊆ U := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    exact hrU (hgapAt x y (image_mono hroomOD hx) (image_mono hroomOD hy))
  apply eqOn_output_positive_side E₂ hO₁ hε hεl hR hOtarget hU hρ.continuousOn hOU
    (fun x hx w hw => (hheight x (hO₁d hx) w
      ((mem_ball_zero_iff.mp hw).trans_le ((half_le_self hR.le).trans (hRa''.trans had.le)))).mono
        (Ioo_subset_Ioo (by linarith) (by linarith))) hg₁ hg₂ hF hG hS₂
    (image_mono subset_union_left) hLeft

end CalderonN
