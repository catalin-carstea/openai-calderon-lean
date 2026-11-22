module

public import Proof.CalderonN.ChartTransferAssembly
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

import Proof.Manuscript.Lemma61
import Proof.CalderonN.DilationJetBounds
import Proof.CalderonN.DilationMetricRecovery
import Proof.CalderonN.MomentInterpolation
import Proof.CalderonN.CylinderSeed
import Mathlib.Tactic

public section

open CalderonN Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 2500000

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem interpolation_scale_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hle : r ≤ s ^ (20 + dim : ℕ)) : r ^ ((1 : ℝ) / (20 + (dim : ℝ))) ≤ s := by
  have hpos : (0 : ℝ) < 20 + (dim : ℝ) := by positivity
  calc
    _ ≤ (s ^ (20 + dim : ℕ)) ^ ((1 : ℝ) / (20 + (dim : ℝ))) :=
      Real.rpow_le_rpow hr hle (by positivity)
    _ = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      push_cast
      rw [mul_one_div_cancel hpos.ne', Real.rpow_one]

/-- Lemma 6.3 of the pinned manuscript for the fixed chart and cutoff,
with the normalized order-eight jet improved to exponent three halves. -/
theorem lemma63 (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {a : ℕ} {u₁ u₂ : Fin a → X dim → ℝ}
    (hu₁ : ∀ i, Harmonic Ω g₁ (u₁ i)) (hu₂ : ∀ i, Harmonic Ω g₂ (u₂ i))
    (hpair : ∀ i, EqOn (u₁ i) (u₂ i) W) (hspan : HessianSpanning g₁ u₁)
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 21 + dim ≤ p)
    {ρ R ε tb K c₀ floor ε₀ C : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (htb : 0 < tb) (hK : 0 < K) (hfloor : 1 ≤ floor) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C)
    (hdepth : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1 / 4)
    (hZ : IsCompact Z) (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hZO : Z ⊆ ball (0 : X dim) 3)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : X dim) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)
    {k : ℕ} {M : Fin (k + 1) → ℝ} {Cj : Fin 9 → ℝ}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hEstimate : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : X dim) 3)
      K ρ c₀ M Cj floor ε₀ C)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :
    ∃ D ρ₀ : ℝ, 0 < D ∧ 0 < ρ₀ ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        let Y := interior (coordinateCylinder normal)
        let K := cylinderCore normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) δ
        let γ := conformalReference (depthScale normal 4) g₁ lam
        let q₂ := dilatedMetric g₂ lam
        Small Y γ q₂ r ε →
        ∀ y ∈ K, r y < ρ₀ → smallJet γ q₂ y ≤ D * (r y) ^ (3 / 2 : ℝ) := by
  let Y := interior (coordinateCylinder normal)
  let L := coordinateCylinder normal
  let J := cylinderCore normal 4 tb
  let depth := conformalDepth normal 4
  let σ := depthScale normal 4
  let χ := cylinderCutoff normal 4 tb
  let c (i : Fin a) := u₁ i 0
  let B (i : Fin a) := fderiv ℝ (u₁ i) 0
  have h₀ : (0 : X dim) ∈ Ω := by
    obtain ⟨_, _, _, hz, hsub, _⟩ := hside
    exact hsub hz
  have hJ : IsCompact J := isCompact_cylinderCore 4 tb
  have hL : IsCompact L := isCompact_coordinateCylinder
  have hJY : J ⊆ Y := cylinderCore_subset_interior htb hdepth
  obtain ⟨s₀, hs₀, hbuffer⟩ := exists_cylinderCore_cutoff_buffer htb hdepth
  obtain ⟨l, hLip⟩ := exists_cylinderDepth_lipschitz (normal := normal) 4
  have hg₁Ω : SmoothMetric Ω g₁ :=
    ⟨fun i j => (hg₁.1 i j).mono (subset_univ Ω), fun x _ => hg₁.2 x (mem_univ _)⟩
  have hg₂Ω : SmoothMetric Ω g₂ :=
    ⟨fun i j => (hg₂.1 i j).mono (subset_univ Ω), fun x _ => hg₂.2 x (mem_univ _)⟩
  obtain ⟨Cr, hCr, hrecover⟩ := exists_uniform_normalized_metric_jet_recovery hΩ h₀ hJ hg₁Ω hg₂Ω
    hchart₁ hchart₂ hu₁ hu₂ hspan (contDiff_depthScale (normal := normal) 4) (depthScale_pos 4)
  obtain ⟨Ci, ρi, hCi, hρi, hinterp⟩ := exists_three_halves_jet_of_weighted_moment hLip hR hp
  obtain ⟨A, hA, hMA⟩ := lemma61 hn hΩ hside hg₁ hg₂ hg₁₀ hg₂₀ hchart₁ hchart₂ hG₁ hG₂
    hmetric hgreen hu₁ hu₂ hpair hE hp hρ hR hε htb hK hfloor hε₀ hC hdepth hZ hCZ hZO
    hNormal hRadius hSetup hEstimate hData
  obtain ⟨M₁, hM₁, hm₁⟩ := exists_uniform_renormalizedHarmonic_jet_bound hΩ h₀ hL
    (fun i => (hu₁ i).1) c B (m := 40 + 2 * dim + 1) (by omega)
  obtain ⟨M₂, hM₂, hm₂⟩ := exists_uniform_renormalizedHarmonic_jet_bound hΩ h₀ hL
    (fun i => (hu₂ i).1) c B (m := 40 + 2 * dim + 1) (by omega)
  let Mj := M₂ + M₁
  have hMj : 0 ≤ Mj := add_nonneg (zero_le_one.trans hM₂) (zero_le_one.trans hM₁)
  let H := Ci * ((((3 / 2 : ℝ)^p)^2) * A + Mj)
  have hH : 0 < H := mul_pos hCi (add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) hA)
    (add_pos (zero_lt_one.trans_le hM₂) (zero_lt_one.trans_le hM₁)))
  let r₀ := min ρi (min 1 (s₀ ^ (20 + dim : ℕ)))
  refine ⟨Cr*H, r₀, mul_pos hCr hH, lt_min hρi (lt_min zero_lt_one (pow_pos hs₀ _)), ?_⟩
  filter_upwards [hrecover, hm₁, hm₂, hMA] with lam hRec hJ₁ hJ₂ hMom hlam
  intro δ hδ
  dsimp only
  intro hsmall y hy hr
  let r := shrinkingRadius R p depth δ
  let T := {z : X dim | lam • z ∈ Ω}
  let v₁ (i : Fin a) := renormalizedHarmonic (c i) (B i) (u₁ i) lam
  let v₂ (i : Fin a) := renormalizedHarmonic (c i) (B i) (u₂ i) lam
  let V (i : Fin a) (z : X dim) := v₂ i z - v₁ i z
  have hT : IsOpen T := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hLT : L ⊆ T := fun z hz => (hJ₁ hlam z hz).1
  have hv₁ (i : Fin a) : ContDiffOn ℝ ∞ (v₁ i) T :=
    contDiffOn_renormalizedHarmonic (hu₁ i).1 (c i) (B i) lam
  have hv₂ (i : Fin a) : ContDiffOn ℝ ∞ (v₂ i) T :=
    contDiffOn_renormalizedHarmonic (hu₂ i).1 (c i) (B i) lam
  have hV (i : Fin a) : ContDiffOn ℝ ∞ (V i) T := (hv₂ i).sub (hv₁ i)
  have hVhigh (i : Fin a) (z : X dim) (hz : z ∈ L) :
      ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) (V i) z‖ ≤ Mj := by
    have hfin : ((40 + 2 * dim + 1 : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr le_top
    rw [fun_iteratedFDeriv_sub_apply
      (((hv₂ i).contDiffAt (hT.mem_nhds (hLT hz))).of_le hfin)
      (((hv₁ i).contDiffAt (hT.mem_nhds (hLT hz))).of_le hfin)]
    exact (norm_sub_le _ _).trans (add_le_add ((hJ₂ hlam z hz).2 i) ((hJ₁ hlam z hz).2 i))
  have hrI : r y < ρi := hr.trans_le (min_le_left _ _)
  have hr₁ : r y ≤ 1 := hr.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrₛ : r y ≤ s₀ ^ (20 + dim : ℕ) :=
    hr.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hposr : 0 < r y := shrinkingRadius_pos hR hδ.1 p depth y
  have hscale := interpolation_scale_le (dim := dim) hposr.le hs₀.le hrₛ
  obtain ⟨hc, ho, hχ⟩ := hbuffer y hy
  have hQo := (ball_subset_ball hscale).trans ho
  have hQc := (closedBall_subset_closedBall hscale).trans hc
  have hjet (i : Fin a) (j : ℕ) (hj : j ≤ 10) :
      ‖iteratedFDeriv ℝ j (V i) y‖ ≤ H * (r y) ^ (3 / 2 : ℝ) :=
    hinterp T hT (interior_subset.trans hLT) (V i) χ (hV i) δ hδ.1 y (hJY hy) A Mj hA hMj
      hrI hr₁ hQo (hQc.trans hLT) (fun x hx => hχ (ball_subset_ball hscale hx))
      (fun x hx => hVhigh i x (hQc hx)) (hMom hlam δ hδ hsmall i) j hj
  have hBound : 0 ≤ H * (r y) ^ (3 / 2 : ℝ) :=
    mul_nonneg hH.le (Real.rpow_nonneg hposr.le _)
  exact ((hRec hlam.ne' y hy).2 _ hBound hjet).trans_eq (by simp only [mul_assoc, r, depth])

end CalderonPaper
