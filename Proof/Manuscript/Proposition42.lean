module

public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.CylinderCutoff
public import Proof.CalderonN.NormalInverse
public import Proof.CalderonN.Radius
public import Proof.CalderonN.MovingTrace
public import Proof.CalderonN.MovingSphere.RadiusSeed

import Proof.Manuscript.LocalGreenChart
import Proof.Manuscript.SphereChartLocality
import Proof.Manuscript.SphereChoices
import Proof.CalderonN.SphereCoercivity
import all Proof.CalderonN.Coordinates
import Mathlib.Tactic

public section

open Set Filter Metric CalderonN
open CalderonN.FixedTube CalderonN.MovingSphere CalderonPaper.SphereLocality CalderonPaper.SphereChoices
open scoped ContDiff Topology

namespace CalderonPaper

set_option maxHeartbeats 3500000 in
/-- Proposition 4.2. The same continued kernel solves the two dilated
equations on an open neighborhood of the normal spheres and retains the
prescribed lower and positive-separation seeds. -/
theorem proposition42
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W)) :
    let Y := coordinateCylinder normal
    let Z := closedBall (0 : X n) (5/2)
    let t := conformalDepth normal 4
    let γ := conformalReference (depthScale normal 4) g₁
    ∃ (ρ tb lam₀ : ℝ) (E : ℝ → (X n) × (X n) → (X n)),
      0 < ρ ∧ 0 < tb ∧ 0 < lam₀ ∧ ContDiff ℝ ∞ (fun q : ℝ × ((X n) × (X n)) => E q.1 q.2) ∧
      (∀ y, t y ≤ 3 * tb → parabolicHeight normal y < 1/4) ∧
      (∀ lam ∈ Icc (-lam₀) lam₀, NormalCoordinates Z (ball (0 : X n) 3)
        (γ lam) (E lam) (fun _ => ρ)) ∧
      ∃ (pmin : ℕ) (εmax : ℕ → ℝ) (Rmax : ℕ → ℝ → ℝ),
        2 ≤ pmin ∧ (∀ p ≥ pmin, 0 < εmax p) ∧
        (∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), 0 < Rmax p ε) ∧
        ∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), ∀ R ∈ Ioc (0 : ℝ) (Rmax p ε),
          let r := shrinkingRadius R p t
          ∃ d C : ℝ, 0 < d ∧ 0 ≤ C ∧
            (∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y, r a y ≤ ρ/2) ∧
            ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
            let N := normalPairDomain (interior Z) (γ lam) ρ (E lam)
            let q₁ := dilatedMetric g₁ lam
            let q₂ := dilatedMetric g₂ lam
            ball (0 : X n) 3 ⊆ {y | lam • y ∈ Ω} ∧
            (∀ a ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y, r a y < ρ ∧ r a y * (beta (γ lam) (r a) y)^2 ≤ ε) ∧
            ∃ (O₀ : Set ((X n) × (X n))) (F : (X n) × (X n) → ℝ),
              IsOpen O₀ ∧ fixedSeparationSet 4 (d/2) ⊆ O₀ ∧
              ProductSolutionOn q₁ q₂ O₀ F ∧ (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ C) ∧
              (∀ δ ∈ Ioc (0 : ℝ) 1, (∀ y ∈ interior Y, smallJet (γ lam) q₂ y ≤ ε * r δ y) →
                ∃ (O : Set ((X n) × (X n))) (G : (X n) × (X n) → ℝ),
                  IsOpen O ∧ ProductSolutionOn q₁ q₂ O G ∧
                  lowerNormalSeed normal N ⊆ O ∧
                  EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) ∧
                  (∀ a ∈ Icc δ 1, ∀ w ∈ bundle Y (γ lam), (endpoint (E lam) (r a) w, w.1) ∈ O) ∧
                  (∀ w ∈ bundle Y (γ lam), tb < t w.1 →
                    let q := (endpoint (E lam) (r δ) w, w.1)
                    q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) ∧
                  ∀ w ∈ bundle Y (γ lam), w.1 normal < -(1/4 : ℝ) →
                    let q := (endpoint (E lam) (r δ) w, w.1)
                    ‖q.1‖ ≤ 3 ∧ ‖q.2‖ ≤ 3 ∧ G =ᶠ[𝓝 q] dilatedGreen G₁ lam) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let Y := coordinateCylinder normal
  let Z := closedBall (0 : X n) (5/2)
  let B := ball (0 : X n) 3
  let B' := ball (0 : X n) 5
  let D₃ := closedBall (0 : X n) 3
  let t := conformalDepth normal 4
  let γ := conformalReference (depthScale normal 4) g₁
  obtain ⟨c, g₁', g₂', hc, hDΩ, hside', hg₁', hg₂', he₁, he₂, hG₁', hG₂', hmetric', hgreen'⟩ :=
    exists_global_alignedGreen_chart hΩ hside hg₁ hg₂ hG₁ hG₂ hmetric hgreen
  let D := ball (0 : X n) c
  let W' := W ∩ D
  let γ' := conformalReference (depthScale normal 4) g₁'
  have hD : IsOpen D := isOpen_ball
  have hW' : IsOpen W' := hW.inter hD
  have h0D : (0 : X n) ∈ D := mem_ball_self hc
  have h1' : g₁' 0 = 1 := (he₁ h0D).trans h₁
  have h2' : g₂' 0 = 1 := (he₂ h0D).trans h₂
  have hYc : IsCompact Y := isCompact_coordinateCylinder (normal := normal)
  have hZc : IsCompact Z := isCompact_closedBall _ _
  have hZB : Z ⊆ B := closedBall_subset_ball (by norm_num)
  have hYZ : Y ⊆ interior Z :=
    (coordinateCylinder_subset_closedBall (normal := normal)).trans
      ((closedBall_subset_ball (by norm_num)).trans
        (isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall))
  have hYB : Y ⊆ B := hYZ.trans (interior_subset.trans hZB)
  have hZcl : closure (interior Z) ⊆ Z := closure_minimal interior_subset isClosed_closedBall
  have hBB' : B ⊆ B' := ball_subset_ball (by norm_num)
  have hB : IsOpen B := isOpen_ball
  have hB' : IsOpen B' := isOpen_ball
  obtain ⟨ρ, τ, E, hρ, hτ, hτ1, hE, hDil, hNorm', hNorm⟩ :=
    exists_actual_compact_normalRoom normal hD h0D hg₁' he₁
  obtain ⟨tb, htb, ht⟩ := exists_cylinderDepth_margin (normal := normal) (L := 4) (by norm_num)
  obtain ⟨p₀, εmax, R₀, hεmax, hR₀, hTest⟩ :=
    exists_uniform_strict_conformal_spheres (normal := normal) (Y := interior Z) (Ω := B) (D := D₃)
      isOpen_interior hB (hZc.of_isClosed_subset isClosed_closure hZcl) (hZcl.trans hZB)
      (isCompact_closedBall _ _) ball_subset_closedBall hg₁' hg₂' h1'
  obtain ⟨Rcap, hRcap, hCap⟩ := uniform_conformal_radius_caps normal hYc hg₁' h1' hρ
  let pmin := max 2 p₀
  let Rmax (p : ℕ) (ε : ℝ) := min (R₀ p ε) (Rcap p ε)
  have hP₂ (p : ℕ) (hp : pmin ≤ p) : 2 ≤ p := (le_max_left _ _).trans hp
  have hP₀ (p : ℕ) (hp : pmin ≤ p) : p₀ ≤ p := (le_max_right _ _).trans hp
  have hRmax (p : ℕ) (hp : pmin ≤ p) (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) (εmax p)) :
      0 < Rmax p ε := lt_min (hR₀ p (hP₀ p hp) ε hε) (hRcap p (hP₂ p hp) ε hε.1)
  refine ⟨ρ, tb, τ, E, hρ, htb, hτ, hE, ht, hNorm, pmin, εmax, Rmax, le_max_left _ _,
    fun p hp => hεmax p (hP₀ p hp), hRmax, ?_⟩
  intro p hp ε hε R hR
  let r := shrinkingRadius R p t
  have hp₀ := hP₀ p hp
  have hp₂ := hP₂ p hp
  have hR₀' : R ∈ Ioc (0 : ℝ) (R₀ p ε) := ⟨hR.1,hR.2.trans (min_le_left _ _)⟩
  have hRc' : R ∈ Ioc (0 : ℝ) (Rcap p ε) := ⟨hR.1,hR.2.trans (min_le_right _ _)⟩
  obtain ⟨hRad, hβ⟩ := hCap p hp₂ ε hε.1 R hRc'
  have hA : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hτA : Icc (-τ) τ ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (neg_lt_zero.mpr hτ) hτ
  have hStrict := ((hTest p hp₀ ε hε R hR₀').and hA).mono fun lam h hpL =>
    h.1 hpL (hE.comp (contDiff_const.prodMk contDiff_id))
      ((hNorm' lam h.2).mono_centers (interior_subset : interior Z ⊆ Z))
  let frames (lam : ℝ) : Frame n := fun y => smoothMetricFrame (γ' lam y)
  have hFrame (lam : ℝ) (y : X n) (i j : I n) :
      metricPair (γ' lam) y (frames lam y i) (frames lam y j) = if i = j then 1 else 0 :=
    smoothMetricFrame_orthonormal (conformalFamily_posDef normal hg₁' lam y) i j
  have heS (i : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => frames q.1 q.2 i) :=
    canonicalFrames_contDiff normal hg₁' i
  obtain ⟨d, C, hd, hC, hSweep⟩ := exists_conformalCylinder_greenContinuation_with_high_seed
    hn hD hW' hside' hg₁' hg₂' h1' h2' hG₁' hG₂' hmetric' hgreen' hZc hYZ hZB hE
    hρ hR.1 hε.1.le htb (show 0 < p by omega) ht hNorm' hRad
    (frames := frames) (fun lam _ => hFrame lam)
    (fun lam _ i => ((heS i).comp (contDiff_const.prodMk contDiff_id)).contDiffOn) hStrict
  refine ⟨d,C,hd,hC,hRad,?_⟩
  dsimp only
  filter_upwards [hτA,hSweep,hβ,hA] with lam hlam hsw hb hlam1 hpos
  let N' := normalPairDomain (interior Z) (γ' lam) ρ (E lam)
  let N := normalPairDomain (interior Z) (γ lam) ρ (E lam)
  let q₁ := dilatedMetric g₁ lam
  let q₂ := dilatedMetric g₂ lam
  let q₁' := dilatedMetric g₁' lam
  let q₂' := dilatedMetric g₂' lam
  have hMap : MapsTo (fun x : X n => lam • x) B' D :=
    (hDil lam hlam).mono_left ball_subset_closedBall
  have hBΩ : B ⊆ {y | lam • y ∈ Ω} := fun _ hy => hDΩ (hMap (hBB' hy))
  have heq₁ : EqOn q₁' q₁ B' := eqOn_dilatedMetric_of_mapsTo he₁ hMap
  have heq₂ : EqOn q₂' q₂ B' := eqOn_dilatedMetric_of_mapsTo he₂ hMap
  have heqγ : EqOn (γ' lam) (γ lam) B' :=
    eqOn_conformalReference_of_dilation (depthScale normal 4) heq₁
  have hN : N' = N := normalPairDomain_congr (heqγ.mono (interior_subset.trans (hZB.trans hBB'))) _ _
  have hBundle : bundle Y (γ' lam) = bundle Y (γ lam) :=
    bundle_congr (heqγ.mono (hYB.trans hBB'))
  have hNsub : N' ⊆ B ×ˢ interior Z :=
    normalPairDomain_subset_of_normalCoordinates interior_subset (hNorm' lam hlam1)
  have hNprod : N' ⊆ B ×ˢ B :=
    hNsub.trans (Set.prod_mono (Subset.refl _) (interior_subset.trans hZB))
  have hClose (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1) (y : X n) (hy : y ∈ Y) :
      r a y < ρ ∧ r a y * (beta (γ lam) (r a) y)^2 ≤ ε := by
    have he := beta_eq_of_metric_eq_at (r := r a) (heqγ (hBB' (hYB hy)))
    exact ⟨(hRad a ha y hy).trans_lt (half_lt_self hρ),
      by rw [← he]; exact hb hpos a ha y hy⟩
  have hFramed (w : X n × X n) (hw : w ∈ bundle Y (γ lam)) (a : ℝ) :
      ∃ v : ↥(standardSphere n),
        (endpoint (E lam) (r a) w, w.1) = normalSpherePoint (E lam) (frames lam) r ((w.1,v),a) := by
    have hw' : w ∈ bundle Y (γ' lam) := hBundle.symm ▸ hw
    obtain ⟨v,hv⟩ := exists_frame_representation (fun y _ => hFrame lam y) hw'
    refine ⟨v,?_⟩
    change (E lam (w.1,r a w.1 • w.2),w.1) = (E lam (w.1,r a w.1 • frameVector (frames lam) w.1 v),w.1)
    rw [hv]
  obtain ⟨O₀, F, hO₀, hFtarget, hFD, hFB, hBuild⟩ := hsw hpos
  let O₀' := O₀ ∩ (B' ×ˢ B')
  have hFtarget' : fixedSeparationSet 4 (d/2) ⊆ O₀' := by
    intro z hz
    exact ⟨hFtarget hz, mem_ball_zero_iff.mpr (hz.1.trans_lt (by norm_num)),
      mem_ball_zero_iff.mpr (hz.2.1.trans_lt (by norm_num))⟩
  have hFD' : ProductSolutionOn q₁ q₂ O₀' F :=
    productSolution_congr_metrics hB' heq₁ heq₂ inter_subset_right (hFD.mono inter_subset_left)
  refine ⟨hBΩ,hClose,O₀',F,hO₀.inter (hB'.prod hB'),hFtarget',hFD',hFB,?_⟩
  intro δ hδ hSmall
  have hSmall' : Small (interior Y) (γ' lam) q₂' (r δ) ε := by
    intro y hy
    have hyB' := hBB' (hYB (interior_subset hy))
    have hJ := smallJet_congrOn hB' heqγ heq₂ hyB'
    exact ⟨hJ ▸ hSmall y hy, hb hpos δ hδ y (interior_subset hy)⟩
  obtain ⟨O,G,hO,hOroom,hG,hSeed,hTop,hBottom⟩ := hBuild δ hδ hSmall'
  let O' := O ∩ (B ×ˢ B)
  have hG' : ProductSolutionOn q₁ q₂ O' G :=
    productSolution_congr_metrics hB (heq₁.mono hBB') (heq₂.mono hBB')
      inter_subset_right (hG.mono inter_subset_left)
  have hLsub : lowerNormalSeed normal N' ⊆ O' := fun z hz => ⟨hOroom (Or.inl hz),hNprod hz.1.1⟩
  have hLseed : EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N') := by
    intro z hz
    exact (hSeed hz).trans (dilatedInitialGreen_inter_eq G₁ G₂ z (hMap (hBB' (hNprod hz.1.1).2)))
  have hLsub' : lowerNormalSeed normal N ⊆ O' := by
    rw [← hN]
    exact hLsub
  have hLseed' : EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal N) := by
    rw [← hN]
    exact hLseed
  refine ⟨O',G,hO.inter (hB.prod hB),hG',hLsub',hLseed',?_,?_,?_⟩
  · intro a ha w hw
    obtain ⟨v,hv⟩ := hFramed w hw a
    refine ⟨hOroom (Or.inr ⟨((w.1,v),a),⟨⟨hw.1,mem_univ _⟩,ha⟩,hv.symm⟩),?_⟩
    have ha' : a ∈ Ioc (0 : ℝ) 1 := ⟨hδ.1.trans_le ha.1,ha.2⟩
    have hw' : w ∈ bundle (interior Z) (γ' lam) :=
      ⟨hYZ hw.1, (show w ∈ bundle Y (γ' lam) from hBundle.symm ▸ hw).2⟩
    exact hNprod (endpoint_mem_normalPairDomain hw' (shrinkingRadius_pos hR.1 ha'.1 p t w.1).le
      (hClose a ha' w.1 hw.1).1)
  · intro w hw hwtop
    obtain ⟨v,hv⟩ := hFramed w hw δ
    change (endpoint (E lam) (r δ) w,w.1) ∈ fixedSeparationSet 3 d ∧
      G =ᶠ[𝓝 (endpoint (E lam) (r δ) w,w.1)] F
    rw [hv]
    exact hTop w.1 hw.1 hwtop v
  · intro w hw hwbottom
    obtain ⟨v,hv⟩ := hFramed w hw δ
    change ‖(endpoint (E lam) (r δ) w,w.1).1‖ ≤ 3 ∧
      ‖(endpoint (E lam) (r δ) w,w.1).2‖ ≤ 3 ∧
      G =ᶠ[𝓝 (endpoint (E lam) (r δ) w,w.1)] dilatedGreen G₁ lam
    rw [hv]
    exact hBottom w.1 hw.1 hwbottom v

end CalderonPaper
