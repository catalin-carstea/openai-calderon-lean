module

public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.FixedTube.Initialization

import Proof.CalderonN.FixedTube.GreenInitialization
import Proof.Manuscript.FixedSeparationJets
import Proof.Manuscript.SeparatedGreenAgreement
import Proof.Manuscript.LocalGreenChart
import Mathlib.Tactic

public section

open Set Filter Metric
open scoped Topology
open CalderonN CalderonN.FixedTube

namespace CalderonPaper

set_option linter.unusedVariables false in
/-- Proposition 3.5. The fixed scale and derivative order are chosen before
the neighborhoods and uniform bounds for the small spatial dilations. -/
theorem proposition35
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (normal : I n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (h₁ : g₁ 0 = 1) (h₂ : g₂ 0 = 1)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {B d η : ℝ} (hB : 0 < B) (hd : 0 < d) (hη : 0 < η) (m : ℕ) :
    ∃ (U V : Set ((X n) × (X n))) (C : ℝ),
      IsOpen U ∧ IsOpen V ∧ fixedSeparationSet B d ⊆ V ∧ closure V ⊆ U ∧
      IsCompact (closure V) ∧ 0 ≤ C ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        U ⊆ OffDiagonal {x | lam • x ∈ Ω} ∧
        ∃ G : (X n) × (X n) → ℝ,
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) U G ∧
          EqOn G (dilatedGreen G₁ lam) {z ∈ U | lam • z.2 ∈ W} ∧
          EqOn G (dilatedGreen G₂ lam) {z ∈ U | lam • z.1 ∈ W} ∧
          EqOn G (dilatedGreen G₁ lam) {z ∈ U | z.2 normal < -η} ∧
          EqOn G (dilatedGreen G₂ lam) {z ∈ U | z.1 normal < -η} ∧
          ∀ k ≤ m, ∀ z ∈ V, ‖iteratedFDeriv ℝ k G z‖ ≤ C := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨r, q₁, q₂, hr, hDΩ, hSide, hq₁, hq₂, he₁, he₂, hD₁, hD₂, hEq, hEqG⟩ :=
    exists_global_alignedGreen_chart hΩ hside hg₁ hg₂ hG₁ hG₂ hmetric hgreen
  let D := ball (0 : X n) r
  let T := W ∩ D
  have hD : IsOpen D := isOpen_ball
  have hT : IsOpen T := hW.inter hD
  have h₀ : (0 : X n) ∈ D := mem_ball_self hr
  have hq₁₀ : q₁ 0 = 1 := (he₁ h₀).trans h₁
  have hq₂₀ : q₂ 0 = 1 := (he₂ h₀).trans h₂
  let e := d/4
  let R := B + 2 + e + η + 3
  have he : 0 < e := by dsimp [e]; positivity
  have heSmall : e < d/2 := by dsimp [e]; linarith
  have hroom : B + 2 + e + η + 2 < R := by dsimp [R]; linarith
  have hR : 0 < R := by linarith
  have hBR : B+2 ≤ R := by linarith
  obtain ⟨CSeed, hCSeed, hSeed⟩ := exists_bounded_fixedSeparation_initialGreen
    (normal := normal) hn hD hT hSide hq₁ hq₂ hq₁₀ hq₂₀ hD₁ hD₂ hEq hEqG hR he hη
  obtain ⟨CJet, hCJet, hJets⟩ := exists_fixedSeparation_jetBound hq₁ hq₂ (B := B) hd m
  let U := openSeparatedRange (n := n) (B+2) (d/2)
  let V := openSeparatedRange (n := n) (B+1) (3*d/4)
  have hU := isOpen_openSeparatedRange (n := n) (B+2) (d/2)
  have hV := isOpen_openSeparatedRange (n := n) (B+1) (3*d/4)
  have hIntoV : fixedSeparationSet B d ⊆ V := fixedSeparationSet_subset_open (by linarith) (by linarith)
  have hVmid : closure V ⊆ fixedSeparationSet (B+1) (3*d/4) :=
    closure_openSeparatedRange_subset_fixed (B+1) (3*d/4)
  have hVbig : closure V ⊆ U := hVmid.trans
    (fixedSeparationSet_subset_open (by linarith) (by linarith))
  have hVcompact : IsCompact (closure V) :=
    (isCompact_fixedSeparationSet (B+1) (3*d/4)).of_isClosed_subset isClosed_closure hVmid
  have hUfixed : U ⊆ fixedSeparationSet (B+2) (d/2) :=
    openSeparatedRange_subset_fixed (B+2) (d/2)
  have hEnlarged : fixedSeparationSet (dim := n) (B+2) (d/2) ⊆ fixedSeparationSet R e :=
    fun _ hz => ⟨hz.1.trans hBR, hz.2.1.trans hBR, heSmall.le.trans hz.2.2⟩
  have hRange : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨U, V, CJet * CSeed, hU, hV, hIntoV, hVbig, hVcompact, mul_nonneg hCJet hCSeed, ?_⟩
  filter_upwards [hSeed, hRange, eventually_dilated_closedBall_mapsTo hD h₀ R,
    eventually_dilated_mem_side_of_negative_coordinate hSide R hη] with lam hSeedLam hLam hMap hLow hp
  obtain ⟨O, G, hO, hWindow, hSol, hAgreement, hPointBound⟩ := hSeedLam hp
  let DL : Set (X n) := {x | lam • x ∈ D}
  have hDL : IsOpen DL := hD.preimage (show Continuous (fun x : X n => lam • x) from
    (continuous_id : Continuous (id : X n → X n)).const_smul lam)
  have hUD : U ⊆ DL ×ˢ DL := by
    intro z hz
    have hb := hEnlarged (hUfixed hz)
    exact ⟨hMap (mem_closedBall_zero_iff.mpr hb.1), hMap (mem_closedBall_zero_iff.mpr hb.2.1)⟩
  have hUΩ : U ⊆ OffDiagonal {x : X n | lam • x ∈ Ω} := by
    intro z hz
    have hsep : d/2 ≤ ‖z.1 - z.2‖ := (hUfixed hz).2.2
    exact ⟨hDΩ (hUD hz).1, hDΩ (hUD hz).2,
      sub_ne_zero.mp (norm_ne_zero_iff.mp ((half_pos hd).trans_le hsep).ne')⟩
  have hEq₁L : EqOn (dilatedMetric q₁ lam) (dilatedMetric g₁ lam) DL := fun _ hx => he₁ hx
  have hEq₂L : EqOn (dilatedMetric q₂ lam) (dilatedMetric g₂ lam) DL := fun _ hx => he₂ hx
  have hSolU := productSolution_congr_metrics hDL hEq₁L hEq₂L hUD
    (hSol.mono (hUfixed.trans (hEnlarged.trans hWindow)))
  have hLowLam := hLow hp
  obtain ⟨hLeft, hRight⟩ := restoreKnownArmAgreement (normal := normal) (by omega : 2 ≤ n)
    hD hq₁ hq₂ hD₁ hD₂ hEqG (B := B+2) (d := d/2) (by linarith) he heSmall hη.le
    hroom hp hMap hLowLam hWindow hSol hAgreement
  refine ⟨hUΩ, G, hSolU, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hLeft ⟨hUfixed hz.1, hz.2, (hUD hz.1).2⟩
  · intro z hz
    exact hRight ⟨hUfixed hz.1, hz.2, (hUD hz.1).1⟩
  · intro z hz
    have hfixed := hUfixed hz.1
    exact hLeft ⟨hfixed, hLowLam _ (mem_closedBall_zero_iff.mpr (hfixed.2.1.trans hBR)) hz.2.le⟩
  · intro z hz
    have hfixed := hUfixed hz.1
    exact hRight ⟨hfixed, hLowLam _ (mem_closedBall_zero_iff.mpr (hfixed.1.trans hBR)) hz.2.le⟩
  · intro k hk z hz
    exact hJets lam hLam hO (hEnlarged.trans hWindow) hSol CSeed hCSeed
      (fun _ hz => hPointBound _ (hEnlarged hz)) k hk z ((openSeparatedRange_subset_fixed _ _) hz)

end CalderonPaper
