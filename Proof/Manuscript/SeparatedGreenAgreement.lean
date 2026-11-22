module

public import Proof.CalderonN.FixedTube.Initialization
public import Proof.CalderonN.LowerCrossGreen
public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.FixedTube.SeparatedAgreement
public import Proof.CalderonN.FixedTube.CoarseOverlapGeometry

import all Proof.CalderonN.DilatedGreenBounds

import Mathlib.Tactic

public section

open Set Filter Metric CalderonN CalderonN.FixedTube
open scoped Topology

namespace CalderonPaper

variable {n : ℕ}

def openSeparatedRange (B d : ℝ) : Set ((X n) × (X n)) :=
  {z | ‖z.1‖ < B ∧ ‖z.2‖ < B ∧ d < ‖z.1 - z.2‖}

theorem isOpen_openSeparatedRange (B d : ℝ) :
    IsOpen (openSeparatedRange (n := n) B d) := by
  exact (isOpen_lt continuous_fst.norm continuous_const).inter
    ((isOpen_lt continuous_snd.norm continuous_const).inter
      (isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm))

theorem openSeparatedRange_subset_fixed (B d : ℝ) :
    openSeparatedRange (n := n) B d ⊆ fixedSeparationSet B d :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

theorem fixedSeparationSet_subset_open {B B' d d' : ℝ} (hB : B < B') (hd : d' < d) :
    fixedSeparationSet (dim := n) B d ⊆ openSeparatedRange B' d' :=
  fun _ hz => ⟨hz.1.trans_lt hB, hz.2.1.trans_lt hB, hd.trans_le hz.2.2⟩

theorem closure_openSeparatedRange_subset_fixed (B d : ℝ) :
    closure (openSeparatedRange (n := n) B d) ⊆ fixedSeparationSet B d :=
  closure_minimal (openSeparatedRange_subset_fixed B d)
    ((isClosed_le continuous_fst.norm continuous_const).inter
      ((isClosed_le continuous_snd.norm continuous_const).inter
        (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)))

/-- Agreement of both normalized Green kernels on the dilated known set. -/
theorem eqOn_dilatedGreen_of_eqOn {W : Set (X n)} {G₁ G₂ : (X n) × (X n) → ℝ}
    (heq : EqOn G₁ G₂ (OffDiagonal W)) {lam : ℝ} (hlam : lam ≠ 0) :
    EqOn (dilatedGreen G₁ lam) (dilatedGreen G₂ lam) (OffDiagonal {x | lam • x ∈ W}) := by
  intro z hz
  have hdistinct : lam • z.1 ≠ lam • z.2 := by
    intro h
    exact hz.2.2 (by simpa only [inv_smul_smul₀ hlam] using congrArg (lam⁻¹ • ·) h)
  exact congrArg (lam ^ (n-2) * ·) (heq (x := (lam • z.1, lam • z.2))
    ⟨hz.1, hz.2.1, hdistinct⟩)

theorem dilatedInitialGreen_eq_right_of_eqOn {W : Set (X n)} {G₁ G₂ : (X n) × (X n) → ℝ}
    (heq : EqOn G₁ G₂ (OffDiagonal W)) {lam : ℝ} (hlam : lam ≠ 0)
    {z : (X n) × (X n)} (hz : z.1 ≠ z.2) (hx : lam • z.1 ∈ W) :
    dilatedInitialGreen W G₁ G₂ lam z = dilatedGreen G₂ lam z := by
  unfold dilatedInitialGreen
  exact initialGreenKernel_eq_right (eqOn_dilatedGreen_of_eqOn heq hlam) hx hz

/-- The common lower comparison ball restores both full known arms
of a separated continuation. -/
theorem restoreKnownArmAgreement [NeZero n] [Nontrivial (Fin n)] (hn : 2 ≤ n)
    {normal : I n} {D T : Set (X n)} (hD : IsOpen D)
    {q₁ q₂ : MetricField n} (hq₁ : SmoothMetric univ q₁) (hq₂ : SmoothMetric univ q₂)
    {G₁ G₂ : (X n) × (X n) → ℝ}
    (hG₁ : GreenGerm D q₁ G₁) (hG₂ : GreenGerm D q₂ G₂) (heq : EqOn G₁ G₂ (OffDiagonal T))
    {B d R e η lam : ℝ} (hB : 0 ≤ B) (he : 0 < e) (hed : e < d) (hη : 0 ≤ η)
    (hroom : B + e + η + 2 < R) (hlam : 0 < lam)
    (hMaps : MapsTo (fun x : X n => lam • x) (closedBall 0 R) D)
    (hLower : ∀ x ∈ closedBall (0 : X n) R, x normal ≤ -η → lam • x ∈ T)
    {O : Set ((X n) × (X n))} {F : (X n) × (X n) → ℝ}
    (hsub : fixedSeparationSet R e ⊆ O)
    (hF : ProductSolutionOn (dilatedMetric q₁ lam) (dilatedMetric q₂ lam) O F)
    (hSeed : EqOn F (dilatedInitialGreen T G₁ G₂ lam)
      (fixedSeparationSet R e ∩ lowerSidePairs normal η)) :
    EqOn F (dilatedGreen G₁ lam) {z ∈ fixedSeparationSet B d | lam • z.2 ∈ T} ∧
    EqOn F (dilatedGreen G₂ lam) {z ∈ fixedSeparationSet B d | lam • z.1 ∈ T} := by
  let DL : Set (X n) := {x | lam • x ∈ D}
  let TL : Set (X n) := {x | lam • x ∈ T}
  have hDL : IsOpen DL := hD.preimage (show Continuous (fun x : X n => lam • x) from
    (continuous_id : Continuous (id : X n → X n)).const_smul lam)
  have hRDL : ball (0 : X n) R ⊆ DL := fun _ hx => hMaps (ball_subset_closedBall hx)
  have hG₁L : GreenGerm DL (dilatedMetric q₁ lam) (dilatedGreen G₁ lam) :=
    hG₁.dilated hn hD (smoothMetric_restrict hq₁ (subset_univ D)) hlam
  have hG₂L : GreenGerm DL (dilatedMetric q₂ lam) (dilatedGreen G₂ lam) :=
    hG₂.dilated hn hD (smoothMetric_restrict hq₂ (subset_univ D)) hlam
  have hEqL : EqOn (dilatedGreen G₁ lam) (dilatedGreen G₂ lam) (OffDiagonal TL) :=
    eqOn_dilatedGreen_of_eqOn heq hlam.ne'
  obtain ⟨L,hL,hLne,hLlow,hLsep⟩ := exists_separated_lower_anchor (normal := normal)
    hB he hη hroom
  have hBL : B < R := by linarith
  have hLTL : L ⊆ TL := fun x hx => hLower x
    (ball_subset_closedBall (hLsep 0 (by simpa using hB) hx).1) (hLlow x hx).le
  have hNorm (x y : X n) (hy : ‖y‖ ≤ B) (hx : x ∈ L) :
      ‖x‖ ≤ R ∧ e < ‖x-y‖ ∧ x ≠ y := by
    have h := hLsep y hy hx
    have hxy : e < ‖x-y‖ := by
      have hh := h.2
      rwa [mem_closedBall, dist_eq_norm, not_le] at hh
    exact ⟨(mem_ball_zero_iff.mp h.1).le, hxy, sub_ne_zero.mp (norm_ne_zero_iff.mp (he.trans hxy).ne')⟩
  refine ⟨eqOn_green_left_of_separated_lower_anchor he hed (by linarith : B+e < R)
      hDL hL hLne hLTL hRDL hLsep
      (smoothMetric_restrict (smoothMetric_dilatedMetric hq₁ lam) (subset_univ DL))
      hG₁L hEqL hsub hF ?_,
    eqOn_green_right_of_separated_lower_anchor he hed (by linarith : B+e < R)
      hDL hL hLne hLTL hRDL hLsep
      (smoothMetric_restrict (smoothMetric_dilatedMetric hq₂ lam) (subset_univ DL))
      hG₂L hEqL hsub hF ?_⟩
  · intro x hx y _ hy
    have hz := hNorm x y hy hx
    exact (hSeed (x := (x,y)) ⟨⟨hz.1,hy.trans hBL.le,hz.2.1.le⟩,
      (min_le_left _ _).trans_lt (hLlow x hx)⟩).trans
      (dilatedInitialGreen_eq_right_of_eqOn heq hlam.ne' hz.2.2 (hLTL hx))
  · intro y hy x _ hx
    have hz := hNorm y x hx hy
    have hs : e ≤ ‖x-y‖ := by rw [norm_sub_rev]; exact hz.2.1.le
    exact (hSeed (x := (x,y)) ⟨⟨hx.trans hBL.le,hz.1,hs⟩,
      (min_le_right _ _).trans_lt (hLlow y hy)⟩).trans
      (dilatedInitialGreen_eq_left G₁ G₂ (hLTL hy))

end CalderonPaper
