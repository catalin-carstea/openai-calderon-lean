module

public import Proof.Manuscript.ScalarPhaseRoom
public import Proof.Manuscript.ScalarPositiveHeight
public import Proof.Manuscript.ScalarCrossInput

import Proof.Manuscript.ScalarProductPhaseGap
import Proof.CalderonN.CompactBounds
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter MeasureTheory CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

open Elliptic.PhaseCoordinates

private theorem CoefficientBound.relax {L : ScalarElliptic n} {D : Set (X n)}
    {a b A B : ℝ} {N : ℕ} (h : L.CoefficientBound D a A N) (hb : b ≤ a) (hB : A ≤ B) :
    L.CoefficientBound D b B N :=
  ⟨fun x hx v => (mul_le_mul_of_nonneg_right hb (sq_nonneg _)).trans (h.1 x hx v),
    fun x hx j hj =>
      let h' := h.2 x hx j hj
      ⟨fun i k => (h'.1 i k).trans hB,fun i => (h'.2.1 i).trans hB,h'.2.2.trans hB⟩⟩

set_option maxHeartbeats 8500000 in
/-- A fixed-reference global-chart realization of the source's
product criterion, including the two compact input arms. -/
theorem exists_global_reference_scalar_productExtension
    {L₁₀ L₂₀ : ScalarElliptic n} (hL₁₀ : L₁₀.SmoothOn univ) (hL₂₀ : L₂₀.SmoothOn univ)
    {U : Set (X n × X n)} (hU : IsOpen U) (z₀ : X n × X n) (hz₀ : z₀ ∈ U)
    {ρ : X n × X n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U) (hρ₀ : ρ z₀ = 0)
    (hstrict : ProductStrictHessianAt L₁₀.metric L₂₀.metric ρ z₀) :
    ∃ (V : Set (X n × X n)) (K₁ K₂ K₃ K₄ : Set (X n)) (ε : ℝ),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ 0 < ε ∧
      IsCompact K₁ ∧ IsCompact K₂ ∧ IsCompact K₃ ∧ IsCompact K₄ ∧
      let K := (K₁ ×ˢ K₂) ∪ (K₃ ×ˢ K₄)
      let admissible := fun (L₁ L₂ : ℝ → ScalarElliptic n) (ρt : ℝ → (X n × X n) → ℝ) =>
        SmoothFamilyOn L₁ univ ∧ SmoothFamilyOn L₂ univ ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) ∧
        L₁ 0 = L₁₀ ∧ L₂ 0 = L₂₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ c ≤ ε ∧ ρt 0 = (fun z => ρ z - c)
      let side := fun (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) => {z ∈ U | 0 < ρt t z}
      (∀ L₁ L₂ ρt, admissible L₁ L₂ ρt →
        ∀ᶠ t in 𝓝 (0 : ℝ), K ⊆ {z ∈ U | ε < ρt t z}) ∧
      (∀ L₁ L₂ ρt, admissible L₁ L₂ ρt → ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F,
        (L₁ t).ProductSolvesOn (L₂ t) (side ρt t) F →
        ∃ G, (L₁ t).ProductSolvesOn (L₂ t) V G ∧ EqOn G F (V ∩ side ρt t)) ∧
      ∀ H ⊆ V, IsCompact H → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ L₁ L₂ ρt, admissible L₁ L₂ ρt →
        ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, (L₁ t).ProductSolvesOn (L₂ t) (side ρt t) F →
        ∀ M : ℝ, 0 ≤ M → (∀ z ∈ K, |F z| ≤ M) →
        ∃ G, (L₁ t).ProductSolvesOn (L₂ t) V G ∧ EqOn G F (V ∩ side ρt t) ∧
          ∀ k ≤ m, ∀ z ∈ H, ‖iteratedFDeriv ℝ k G z‖ ≤ C*M := by
  obtain ⟨θ₁,θ₂,K,c,r,hθ₁,hθ₂,hθ₁₀,hθ₂₀,_,hjet₂,hs₁,hs₂,_,hc,hr,hrU,hgap,hsign⟩ :=
    exists_local_productPhase_gap_all hL₁₀.1 hL₂₀.1 hU z₀ hz₀ hρ hρ₀ hstrict
  obtain ⟨E₁,hE₁p,hE₁,a₁,k₁,ha₁,hk₁,hbig₁,hinterp₁⟩ :=
    exists_reference_scalar_phaseRoom_interpolation hL₁₀ hθ₁ z₀.1 hθ₁₀ hs₁
  obtain ⟨E₂,hE₂p,hE₂,a₂,k₂,ha₂,hk₂,hbig₂,hinterp₂⟩ :=
    exists_reference_scalar_phaseRoom_interpolation hL₂₀ hθ₂ z₀.2 hθ₂₀ hs₂
  obtain ⟨h₁z,h₁t⟩ := chart_symm_zero E₁ hE₁ (map_zero _) hθ₁₀ hE₁p
  obtain ⟨h₂z,h₂t⟩ := chart_symm_zero E₂ hE₂ (map_zero _) hθ₂₀ hE₂p
  have hℓ₂ : fderiv ℝ θ₂ z₀.2 ≠ 0 := fun h => hs₂.1 (funext fun i => by simp [coordDeriv,h])
  obtain ⟨d,hd,hheight⟩ := exists_reference_monotone_second_height hU z₀ hz₀ hρ hθ₂ hθ₂₀ hℓ₂ hjet₂ E₂ hE₂p hE₂
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
  have hgapAt (x y : (X n)) (hx : x ∈ E₁.symm '' closedD l ε R) (hy : y ∈ E₂.symm '' closedD l ε R) :
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

  let Cross := (closure D₁ ×ˢ closure S₂) ∪ (closure S₁ ×ˢ closure D₂)
  have hCrossComp : IsCompact Cross := (hcD₁.prod hcS₂).union (hcS₁.prod hcD₂)
  have hCrossRef : Cross ⊆ V := union_subset hArm₁ hArm₂
  have hCrossU : Cross ⊆ U := fun z hz => (hCrossRef hz).1
  obtain ⟨η,hη,hMargin⟩ := Carleman.exists_pos_lower_of_compact hCrossComp
    (hρ.continuousOn.mono hCrossU) (fun z hz => (hCrossRef hz).2)
  let margin := η/4
  have hmarg : 0 < margin := by dsimp [margin]; positivity
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
  let adm := fun (L₁ L₂ : ℝ → ScalarElliptic n) (ρt : ℝ → (X n × X n) → ℝ) =>
    SmoothFamilyOn L₁ univ ∧ SmoothFamilyOn L₂ univ ∧
    ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) ∧
    L₁ 0 = L₁₀ ∧ L₂ 0 = L₂₀ ∧
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ margin ∧ ρt 0 = (fun z => ρ z - c)
  let side := fun (ρt : ℝ → (X n × X n) → ℝ) (t : ℝ) => {z ∈ U | 0 < ρt t z}
  have hArms (L₁ L₂ ρt) (hAdm : adm L₁ L₂ ρt) :
      ∀ᶠ t in 𝓝 (0 : ℝ), Cross ⊆ {z ∈ U | margin < ρt t z} := by
    have h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ Cross, margin < ρt t z := by
      apply hCrossComp.eventually_forall_of_forall_eventually
      intro z hz
      have hUZ : ((0 : ℝ),z) ∈ univ ×ˢ U := ⟨mem_univ _,hCrossU hz⟩
      have hAt := hAdm.2.2.1.continuousOn.continuousAt ((isOpen_univ.prod hU).mem_nhds hUZ)
      have hPt : margin < ρt 0 z := by
        obtain ⟨c,_,hc,hec⟩ := hAdm.2.2.2.2.2
        rw [hec]
        have hz' := hMargin z hz
        dsimp [margin] at *
        linarith
      exact hAt.preimage_mem_nhds (Ioi_mem_nhds hPt)
    exact h.mono (fun _ h z hz => ⟨hCrossU hz,h z hz⟩)
  obtain ⟨E₀,hE₀,hCrossData⟩ := exists_scalar_crossData_of_compact_arms
    hD₁ hD₂ hS₁ hS₂ hcD₁ hcD₂ hcS₁ hcS₂
  obtain ⟨A₁,γ₁,hA₁,hγ₁,hγ₁',hI₁⟩ := hi₁
  obtain ⟨A₂,γ₂,hA₂,hγ₂,hγ₂',hI₂⟩ := hi₂
  let β := γ₁+γ₂-1
  have hβ : 0 < β := by dsimp [β]; linarith
  have hQuant : ∀ H ⊆ O₁ ×ˢ O₂, IsCompact H → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ L₁ L₂ ρt, adm L₁ L₂ ρt →
        ∀ᶠ t in 𝓝 (0 : ℝ), ∀ F, (L₁ t).ProductSolvesOn (L₂ t) (side ρt t) F →
        ∀ M : ℝ, 0 ≤ M → (∀ z ∈ Cross, |F z| ≤ M) →
        ∃ G, (L₁ t).ProductSolvesOn (L₂ t) (O₁ ×ˢ O₂) G ∧ EqOn G F ((O₁ ×ˢ O₂) ∩ side ρt t) ∧
          ∀ k ≤ m, ∀ z ∈ H, ‖iteratedFDeriv ℝ k G z‖ ≤ C*M := by
    intro H hH hHc m
    obtain ⟨N,hNumeric⟩ := exists_numeric_scalar_crossExtension hD₁ hD₂
      ⟨hsd₁.mono hS₁D₁,hpc₁⟩ ⟨hsd₂.mono hS₂D₂,hpc₂⟩
      ((measure_mono subset_closure).trans_lt hcD₂.measure_lt_top).ne
      hS₁ hS₂ hsd₁ hsd₂ hO₁ hO₂ hcS₁ hsubS₁ hS₂D₂ hO₁D₁ hO₂D₂
      hA₁.le hA₂.le β hβ hH hHc m
    obtain ⟨lo₁,hi₁,hlo₁,hhi₁,hB₁⟩ := exists_reference_scalar_coefficient_budget hcD₁ hL₁₀ N
    obtain ⟨lo₂,hi₂,hlo₂,hhi₂,hB₂⟩ := exists_reference_scalar_coefficient_budget hcD₂ hL₂₀ N
    obtain ⟨C,hC,hE⟩ := hNumeric (min lo₁ lo₂) (max hi₁ hi₂)
      (lt_min hlo₁ hlo₂) (hhi₁.trans_le (le_max_left _ _))
    refine ⟨C*E₀,mul_nonneg hC hE₀,?_⟩
    intro L₁ L₂ ρt hAdm
    have hA := hArms L₁ L₂ ρt hAdm
    obtain ⟨hL₁,hL₂,hρt,he₁,he₂,c,_,_,heρ⟩ := hAdm
    let ρt' (t : ℝ) (z : X n × X n) := ρt t z + c
    have hρtC : ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt' q.1 q.2) (univ ×ˢ U) :=
      hρt.add contDiffOn_const
    have heρ' : ρt' 0 = ρ := by funext z; simp [ρt',heρ]
    filter_upwards [hA,hheight ρt' hρtC heρ',
      hI₁ L₁ hL₁ he₁,hI₂ L₂ hL₂ he₂,hB₁ L₁ hL₁ he₁,hB₂ L₂ hL₂ he₂]
      with t hArm hHeight hInt₁ hInt₂ hCoef₁ hCoef₂ F hF M hM hBound
    have hArm' : Cross ⊆ side ρt t := fun z hz => ⟨(hArm hz).1,hmarg.trans (hArm hz).2⟩
    have hData := hCrossData hArm' hF M hM hBound
    obtain ⟨G,hG,hGjet⟩ := hE γ₁ γ₂ ((by norm_num : 0 < (1/2:ℝ)).trans hγ₂) hγ₂'.le
      (by dsimp [β]; linarith) (L₁ t) (L₂ t)
      ((hL₁.1 t).restrict (subset_univ _)) ((hL₂.1 t).restrict (subset_univ _))
      ((hCoef₁.mono subset_closure le_rfl).relax (min_le_left _ _) (le_max_left _ _))
      ((hCoef₂.mono subset_closure le_rfl).relax (min_le_right _ _) (le_max_right _ _))
      hInt₁ hInt₂ F (E₀*M) hData
    have hρt' : ContDiffOn ℝ ∞ (ρt t) U :=
      hρt.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => ⟨mem_univ _,hx⟩)
    refine ⟨G,hG.1,?_,fun k hk z hz => (hGjet k hk z hz).trans_eq (by ring)⟩
    exact eqOn_scalar_output_positive_side E₂ hO₁ hε hεl hR hOtarget hU hρt'.continuousOn hOU
      (fun x hx w hw => by
        have hM := (hHeight x (hO₁d hx) w
          ((mem_ball_zero_iff.mp hw).trans_le ((half_le_self hR.le).trans (hRa''.trans had.le)))).mono
            (Ioo_subset_Ioo (by linarith : -d ≤ -ε) (by linarith [hla,had] : l + 3*ε/2 ≤ d))
        intro s hs t' ht' hst
        exact lt_of_add_lt_add_right (hM hs ht' hst))
      (hL₁.1 t) (hL₂.1 t) hF hG.1 hS₂
      (image_mono subset_union_left) hG.2.1
  refine ⟨O₁ ×ˢ O₂,closure D₁,closure S₂,closure S₁,closure D₂,margin,
    hO₁.prod hO₂,⟨hO₁z,hO₂z⟩,hOU,hmarg,hcD₁,hcS₂,hcS₁,hcD₂,hArms,?_,hQuant⟩
  intro L₁ L₂ ρt hAdm
  obtain ⟨_,_,hE⟩ := hQuant ∅ (empty_subset _) isCompact_empty 0
  filter_upwards [hE L₁ L₂ ρt hAdm,hArms L₁ L₂ ρt hAdm] with t ht hK F hF
  obtain ⟨M,hM⟩ := hCrossComp.exists_bound_of_continuousOn
    (hF.1.continuousOn.mono (fun z hz => ⟨(hK hz).1,hmarg.trans (hK hz).2⟩))
  obtain ⟨G,hG,hEq,_⟩ := ht F hF (max M 0) (le_max_right _ _)
    (fun z hz => by simpa only [Real.norm_eq_abs] using (hM z hz).trans (le_max_left _ _))
  exact ⟨G,hG,hEq⟩

end CalderonPaper.ScalarElliptic
