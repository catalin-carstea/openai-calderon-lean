module

public import Proof.CalderonN.FixedTube.Initialization

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped Convex ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- A ball with a strictly contained concentric or off-center closed ball
removed is connected. Each point can move radially to one common sphere
without crossing the removed ball. -/
theorem isConnected_ball_sdiff_closedBall {y : (X dim)} {d R : ℝ}
    (hd : 0 < d) (hroom : ‖y‖+d < R) :
    IsConnected (ball (0 : (X dim)) R \ closedBall y d) := by
  let r := (d + (R - ‖y‖)) / 2
  have hdr : d < r := by dsimp only [r]; linarith
  have hr : 0 < r := hd.trans hdr
  have hR : r + ‖y‖ < R := by dsimp only [r]; linarith
  let D := ball (0 : (X dim)) R \ closedBall y d
  have hdim : 1 < Module.rank ℝ (X dim) := by
    rw [← Module.finrank_eq_rank]
    have hn : 1 < dim := by simpa only [Fintype.card_fin] using Fintype.one_lt_card (α := Fin dim)
    exact_mod_cast (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hn :
      1 < Module.finrank ℝ (X dim))
  have hsphere := isPathConnected_sphere hdim y hr.le
  have hSD : sphere y r ⊆ D := by
    intro z hz
    have hzy : dist z y = r := mem_sphere.mp hz
    refine ⟨?_,fun hz' => (not_le_of_gt hdr) (hzy ▸ mem_closedBall.mp hz')⟩
    have h := dist_triangle z y (0 : (X dim))
    rw [hzy,dist_zero_right,dist_zero_right] at h
    exact mem_ball_zero_iff.mpr (h.trans_lt hR)
  have localPath (x : (X dim)) (hx : x ∈ D) : ∃ z ∈ sphere y r, JoinedIn D x z := by
    let b := x-y
    let t := r / ‖b‖
    let z := y + t • b
    have hb : d < ‖b‖ := by
      rw [show ‖b‖ = dist x y from (dist_eq_norm x y).symm]
      exact lt_of_not_ge fun h => hx.2 (mem_closedBall.mpr h)
    have hpos := hd.trans hb
    have ht : 0 < t := div_pos hr hpos
    have hn : ‖t • b‖ = r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      exact div_mul_cancel₀ r hpos.ne'
    have hz : z ∈ sphere y r := by rwa [mem_sphere,dist_eq_norm,show z-y = t • b by simp [z]]
    refine ⟨z,hz,JoinedIn.of_segment_subset ?_⟩
    intro w hw
    have hwB := (convex_ball (0 : (X dim)) R).segment_subset hx.1 (hSD hz).1 hw
    refine ⟨hwB,?_⟩
    obtain ⟨u,v,hu,hv,huv,rfl⟩ := hw
    have hxb : x = y + b := by dsimp only [b]; abel
    have hrel : u • x + v • z - y = (u + v*t) • b := calc
      _ = (u • y + v • y - y) + (u • b + (v*t) • b) := by
        conv_lhs => rw [hxb]
        simp only [z,smul_add,smul_smul]
        abel
      _ = _ := by rw [← add_smul u v y,huv,one_smul,sub_self,zero_add,← add_smul]
    have hs : d < u*‖b‖+v*r := by
      rcases eq_or_lt_of_le hu with he | hp
      · have hv1 : v = 1 := by linarith
        simpa [← he,hv1] using hdr
      · have h1 := mul_lt_mul_of_pos_left hb hp
        have h2 := mul_le_mul_of_nonneg_left hdr.le hv
        have heq : u*d+v*d = d := by rw [← add_mul,huv,one_mul]
        linarith only [h1,h2,heq]
    have hn' : ‖u • x + v • z - y‖ = u*‖b‖+v*r := by
      rw [hrel,norm_smul,Real.norm_eq_abs,abs_of_nonneg (add_nonneg hu (mul_nonneg hv ht.le))]
      dsimp only [t]
      rw [add_mul,mul_assoc,div_mul_cancel₀ r hpos.ne']
    rw [mem_closedBall,dist_eq_norm,hn']
    exact not_le_of_gt hs
  apply IsPathConnected.isConnected
  apply isPathConnected_iff.mpr
  refine ⟨hsphere.nonempty.mono hSD,?_⟩
  intro x hx z hz
  obtain ⟨x',hx',hxx'⟩ := localPath x hx
  obtain ⟨z',hz',hzz'⟩ := localPath z hz
  exact hxx'.trans (((hsphere.joinedIn x' hx' z' hz').mono hSD).trans hzz'.symm)

/-- On fixed separated slices a lower open comparison identifies the
continuation with the original Green kernel by scalar unique continuation. -/
theorem eqOn_green_left_of_separated_lower_anchor
    {B d R e : ℝ} (he : 0 < e) (hed : e < d) (hroom : B+e < R)
    {Ω W L : Set (X dim)} (hΩ : IsOpen Ω) (hL : IsOpen L) (hLne : L.Nonempty) (hLW : L ⊆ W)
    (hRΩ : ball (0 : (X dim)) R ⊆ Ω)
    (hLsep : ∀ y : (X dim), ‖y‖ ≤ B → L ⊆ ball (0 : (X dim)) R \ closedBall y e)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω g₁)
    {F G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁)
    (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {O : Set ((X dim) × (X dim))} (hO : fixedSeparationSet R e ⊆ O)
    (hF : ProductSolutionOn g₁ g₂ O F)
    (hanchor : ∀ x ∈ L, ∀ y ∈ W, ‖y‖ ≤ B → F (x,y) = G₂ (x,y)) :
    EqOn F G₁ {p ∈ fixedSeparationSet B d | p.2 ∈ W} := by
  rintro ⟨x,y⟩ ⟨hxy,hyW⟩
  let D := ball (0 : (X dim)) R \ closedBall y e
  have hyR : ‖y‖ < R := hxy.2.1.trans_lt (by linarith)
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDΩ : D ⊆ Ω := fun _ hx => hRΩ hx.1
  have hgD : SmoothMetric D g₁ := ⟨fun i j => (hg₁.1 i j).mono hDΩ,fun z hz => hg₁.2 z (hDΩ hz)⟩
  have hDconn := isConnected_ball_sdiff_closedBall he
    (show ‖y‖+e < R from (add_le_add hxy.2.1 (le_refl e)).trans_lt hroom)
  have hslice : Harmonic D g₁ (fun z => F (z,y)) := by
    have hsub : D ×ˢ {y} ⊆ O := by
      rintro ⟨z,t⟩ ⟨hz,ht⟩
      have ht' : t = y := mem_singleton_iff.mp ht
      subst t
      apply hO
      refine ⟨(mem_ball_zero_iff.mp hz.1).le,hyR.le,?_⟩
      rw [← dist_eq_norm]
      exact (lt_of_not_ge (fun h => hz.2 (mem_closedBall.mpr h))).le
    exact (hF.mono hsub).harmonic_left (mem_singleton y)
  have hn (z : (X dim)) (hz : z ∈ D) : z ≠ y := by
    intro hzy
    exact hz.2 (hzy ▸ mem_closedBall_self he.le)
  have hG : Harmonic D g₁ (fun z => G₁ (z,y)) := by
    have h := hG₁.harmonic_left hΩ hg₁ (hRΩ (mem_ball_zero_iff.mpr hyR))
    have hsub : D ⊆ Ω \ {y} := fun z hz => ⟨hDΩ hz,hn z hz⟩
    exact ⟨h.1.mono hsub,fun z hz => h.2 z (hsub hz)⟩
  have heq : EqOn (fun z => F (z,y)) (fun z => G₁ (z,y)) L := by
    intro z hz
    exact (hanchor z hz y hyW hxy.2.1).trans
      (hgreen (x := (z,y)) ⟨hLW hz,hyW,hn z (hLsep y hxy.2.1 hz)⟩).symm
  apply harmonic_eqOn_of_eqOn_open hD hDconn hL hLne (hLsep y hxy.2.1) hgD hslice hG heq
  refine ⟨mem_ball_zero_iff.mpr (hxy.1.trans_lt (by linarith)),?_⟩
  intro hx
  have hs : ‖x-y‖ ≤ e := by rwa [mem_closedBall,dist_eq_norm] at hx
  exact (not_lt_of_ge (hxy.2.2.trans hs)) hed

/-- A single lower comparison ball is disjoint from every removed ball of
the smaller radius for centers in the prescribed target range. -/
theorem exists_separated_lower_anchor {B e η R : ℝ}
    (hB : 0 ≤ B) (he : 0 < e) (hη : 0 ≤ η) (hR : B+e+η+2 < R) :
    ∃ L : Set (X dim), IsOpen L ∧ L.Nonempty ∧ (∀ x ∈ L, x normal < -η) ∧
      ∀ y : (X dim), ‖y‖ ≤ B → L ⊆ ball (0 : (X dim)) R \ closedBall y e := by
  let a : ℝ := B+e+η+1
  let c := (-a) • axis normal
  let L := ball c (1/4)
  have ha : 0 < a := by dsimp only [a]; linarith
  have hc : ‖c‖ = a := by
    rw [show c = (-a) • axis normal from rfl,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ha]
    simp [axis]
  have hc₂ : c normal = -a := by simp [c,axis,PiLp.smul_apply]
  refine ⟨L,isOpen_ball,⟨c,mem_ball_self (by norm_num)⟩,?_,?_⟩
  · intro x hx
    have hn : ‖x-c‖ < 1/4 := by rwa [← dist_eq_norm]
    have h₂ := (abs_coord_le_norm (x-c) normal).trans_lt hn
    simp only [PiLp.sub_apply,hc₂] at h₂
    dsimp only [a] at hc₂ h₂
    linarith [(abs_lt.mp h₂).2]
  · intro y hy x hx
    have hn : ‖x-c‖ < 1/4 := by rwa [← dist_eq_norm]
    have hu := norm_sub_norm_le x c
    have hl := norm_sub_norm_le c x
    rw [hc] at hu hl
    rw [norm_sub_rev] at hl
    refine ⟨mem_ball_zero_iff.mpr (by dsimp only [a] at hu; linarith),?_⟩
    rw [mem_closedBall,dist_eq_norm]
    intro hx'
    have hxy := norm_sub_norm_le x y
    dsimp only [a] at hl
    linarith

/-- The corresponding lower comparison in the second variable recovers
the other original Green kernel on the fixed-separation target. -/
theorem eqOn_green_right_of_separated_lower_anchor
    {B d R e : ℝ} (he : 0 < e) (hed : e < d) (hroom : B+e < R)
    {Ω W L : Set (X dim)} (hΩ : IsOpen Ω) (hL : IsOpen L) (hLne : L.Nonempty) (hLW : L ⊆ W)
    (hRΩ : ball (0 : (X dim)) R ⊆ Ω)
    (hLsep : ∀ x : (X dim), ‖x‖ ≤ B → L ⊆ ball (0 : (X dim)) R \ closedBall x e)
    {g₁ g₂ : (MetricField dim)} (hg₂ : SmoothMetric Ω g₂)
    {F G₁ G₂ : (X dim) × (X dim) → ℝ} (hG₂ : GreenGerm Ω g₂ G₂)
    (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {O : Set ((X dim) × (X dim))} (hO : fixedSeparationSet R e ⊆ O)
    (hF : ProductSolutionOn g₁ g₂ O F)
    (hanchor : ∀ y ∈ L, ∀ x ∈ W, ‖x‖ ≤ B → F (x,y) = G₁ (x,y)) :
    EqOn F G₂ {p ∈ fixedSeparationSet B d | p.1 ∈ W} := by
  rintro ⟨x,y⟩ ⟨hxy,hxW⟩
  let D := ball (0 : (X dim)) R \ closedBall x e
  have hxR : ‖x‖ < R := hxy.1.trans_lt (by linarith)
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDΩ : D ⊆ Ω := fun _ hx => hRΩ hx.1
  have hgD : SmoothMetric D g₂ := ⟨fun i j => (hg₂.1 i j).mono hDΩ,fun z hz => hg₂.2 z (hDΩ hz)⟩
  have hDconn := isConnected_ball_sdiff_closedBall he
    (show ‖x‖+e < R from (add_le_add hxy.1 (le_refl e)).trans_lt hroom)
  have hslice : Harmonic D g₂ (fun z => F (x,z)) := by
    have hsub : {x} ×ˢ D ⊆ O := by
      rintro ⟨t,z⟩ ⟨ht,hz⟩
      have ht' : t = x := mem_singleton_iff.mp ht
      subst t
      apply hO
      refine ⟨hxR.le,(mem_ball_zero_iff.mp hz.1).le,?_⟩
      rw [norm_sub_rev x z,← dist_eq_norm]
      exact (lt_of_not_ge (fun h => hz.2 (mem_closedBall.mpr h))).le
    exact (hF.mono hsub).harmonic_right (mem_singleton x)
  have hn (z : (X dim)) (hz : z ∈ D) : z ≠ x := by
    intro hzx
    exact hz.2 (hzx ▸ mem_closedBall_self he.le)
  have hG : Harmonic D g₂ (fun z => G₂ (x,z)) := by
    have h := hG₂.harmonic_right hΩ hg₂ (hRΩ (mem_ball_zero_iff.mpr hxR))
    have hsub : D ⊆ Ω \ {x} := fun z hz => ⟨hDΩ hz,hn z hz⟩
    exact ⟨h.1.mono hsub,fun z hz => h.2 z (hsub hz)⟩
  have heq : EqOn (fun z => F (x,z)) (fun z => G₂ (x,z)) L := by
    intro z hz
    exact (hanchor z hz x hxW hxy.1).trans
      (hgreen (x := (x,z)) ⟨hxW,hLW hz,(hn z (hLsep x hxy.1 hz)).symm⟩)
  apply harmonic_eqOn_of_eqOn_open hD hDconn hL hLne (hLsep x hxy.1) hgD hslice hG heq
  refine ⟨mem_ball_zero_iff.mpr (hxy.2.1.trans_lt (by linarith)),?_⟩
  intro hy
  have hs : ‖x-y‖ ≤ e := by rwa [mem_closedBall,dist_eq_norm,norm_sub_rev y x] at hy
  exact (not_lt_of_ge (hxy.2.2.trans hs)) hed

end CalderonN.FixedTube
