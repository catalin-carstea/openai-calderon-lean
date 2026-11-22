module

public import Proof.CalderonN.DilationConnection
public import Proof.CalderonN.DilationHarmonic
public import Proof.CalderonN.MomentInterpolation

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.DilationJetBounds
import Proof.CalderonN.DilationMetricRecovery
import Proof.CalderonN.MetricAgreement
import Proof.CalderonN.DilationSmallJet
import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity

public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped BigOperators ContDiff ENNReal Topology

namespace CalderonN

set_option maxHeartbeats 1600000

variable {dim : ℕ} [NeZero dim]

private theorem interpolation_scale_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hle : r ≤ s ^ (20 + dim : ℕ)) : r ^ ((1 : ℝ) / (20 + (dim : ℝ))) ≤ s := by
  have hpos : (0 : ℝ) < 20 + (dim : ℝ) := by positivity
  calc
    _ ≤ (s ^ (20 + dim : ℕ)) ^ ((1 : ℝ) / (20 + (dim : ℝ))) := Real.rpow_le_rpow hr hle (by positivity)
    _ = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      push_cast
      rw [mul_one_div_cancel hpos.ne', Real.rpow_one]

/-- Conditional end of Sections 5 and 6. The moving-sphere producer supplies
the weighted moments on the same chart and for the same radii as the
bootstrap. One positive dilation is chosen after the improvement constants. -/
theorem exists_ball_metric_eq_of_uniform_weighted_moment (hn : 3 ≤ dim)
    {Ω W Y K L : Set (X dim)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hside : ContainsSmoothSide Ω W)
    (hK : IsCompact K) (hL : IsCompact L) (hKY : K ⊆ Y) (hYL : Y ⊆ L)
    (h₀K : (0 : (X dim)) ∈ interior K)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    (hmatch : EqOn g₁ g₂ W)
    {n : ℕ} {u₁ u₂ : Fin n → (X dim) → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hspan : HessianSpanning g₁ u₁)
    {σ χ depth : (X dim) → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσpos : ∀ y, 0 < σ y)
    {l : NNReal} (hdepth : LipschitzOnWith l depth Y) (hdepth₀ : depth 0 < 0)
    {b s₀ : ℝ} (hb : 0 < b) (hs₀ : 0 < s₀)
    (hbuffer : ∀ y ∈ K, closedBall y s₀ ⊆ L ∧ ball y s₀ ⊆ Y ∧ EqOn χ 1 (ball y s₀))
    (hoff : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ y ∈ Y \ K, lam • y ∈ W ∨ b ≤ depth y)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {p : ℕ} (hp : 21 + dim ≤ p)
    (hβ : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
      shrinkingRadius R p depth δ y * (beta (conformalReference σ g₁ lam)
        (shrinkingRadius R p depth δ) y)^2 ≤ ε)
    (hmoment : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        Small Y (conformalReference σ g₁ lam) (dilatedMetric g₂ lam)
          (shrinkingRadius R p depth δ) ε →
        ∀ a, eLpNorm (fun z =>
          χ z * (renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₂ a) lam z -
            renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₁ a) lam z) /
            (shrinkingRadius R p depth δ z)^2) 2 (volume.restrict Y) ≤ ENNReal.ofReal A) :
    ∃ r > 0, ball (0 : (X dim)) r ⊆ Ω ∧ EqOn g₁ g₂ (ball 0 r) := by
  have h₀ : (0 : (X dim)) ∈ Ω := by
    obtain ⟨_, _, _, hz, hs, _⟩ := hside
    exact hs hz
  have hmatch₀ : g₁ 0 = g₂ 0 := by
    ext i j
    exact eq_at_origin_of_eqOn_side hside
      ((hg₁.1 i j).continuousOn.continuousAt (hΩ.mem_nhds h₀))
      ((hg₂.1 i j).continuousOn.continuousAt (hΩ.mem_nhds h₀))
      (fun x hx => congrArg (fun M : (Mat dim) => M i j) (hmatch hx))
  obtain ⟨Cr, hCr, hrecover⟩ := exists_uniform_normalized_metric_jet_recovery
    hΩ h₀ hK hg₁ hg₂ hchart₁ hchart₂ hu₁ hu₂ hspan hσ hσpos
  obtain ⟨Ci, ρi, hCi, hρi, hinterp⟩ := exists_three_halves_jet_of_weighted_moment hdepth hR hp
  obtain ⟨A, hA, hMA⟩ := hmoment
  let c (a : Fin n) := u₁ a 0
  let B (a : Fin n) := fderiv ℝ (u₁ a) 0
  obtain ⟨M₁, hM₁, hm₁⟩ := exists_uniform_renormalizedHarmonic_jet_bound hΩ h₀ hL
    (fun a => (hu₁ a).1) c B (m := (40 + 2 * dim + 1)) (by omega)
  obtain ⟨M₂, hM₂, hm₂⟩ := exists_uniform_renormalizedHarmonic_jet_bound hΩ h₀ hL
    (fun a => (hu₂ a).1) c B (m := (40 + 2 * dim + 1)) (by omega)
  let M := M₂ + M₁
  have hM : 0 ≤ M := add_nonneg (zero_le_one.trans hM₂) (zero_le_one.trans hM₁)
  let Ci' := Ci * ((((3 / 2 : ℝ)^p)^2) * A + M)
  have hCi' : 0 ≤ Ci' := by dsimp only [Ci']; positivity
  let C := Cr * Ci'
  have hC : 0 ≤ C := mul_nonneg hCr.le hCi'
  let ρ₀ := min ρi (min 1 (s₀ ^ (20 + dim : ℕ)))
  have hρ₀ : 0 < ρ₀ := lt_min hρi (lt_min zero_lt_one (pow_pos hs₀ _))
  obtain ⟨ρ, hρ, hρ₀ρ, hsplit⟩ := exists_split_radius hC hε hρ₀
  have hKd : ContinuousOn depth K := hdepth.continuousOn.mono hKY
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨0, interior_subset h₀K⟩
    ((shrinkingRadius_continuousOn R p hKd).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨mem_Ioc.mpr ⟨zero_lt_one, le_rfl⟩, hy⟩))
  let rmin := shrinkingRadius R p depth 1 z
  have hrmin : 0 < rmin := shrinkingRadius_pos hR zero_lt_one p depth z
  let τ := min (ε * rmin) (min (ε / 2 * ρ) (ε / 2 * (R * b ^ p)))
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτ₁ : τ ≤ ε * rmin := min_le_left _ _
  have hτρ : τ ≤ ε / 2 * ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hτb : τ ≤ ε / 2 * (R * b ^ p) := (min_le_right _ _).trans (min_le_right _ _)
  have hs := eventually_smallJet_le_of_common_origin hΩ h₀ hL hg₁ hg₂ hmatch₀ hσ hσpos hτ
  have hnear := ((((((hrecover.and hm₁).and hm₂).and hs).and hoff).and hβ).and hMA)
  obtain ⟨eta, heta, hchoose⟩ := Metric.mem_nhds_iff.mp hnear
  let lam := eta / 2
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hballLam : lam ∈ ball (0 : ℝ) eta := by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hlam]
    dsimp only [lam]
    linarith
  obtain ⟨⟨⟨⟨⟨⟨hRec, hJ₁⟩, hJ₂⟩, hS⟩, hOff⟩, hBeta⟩, hMom⟩ := hchoose hballLam
  let T : Set (X dim) := {z | lam • z ∈ Ω}
  let γ := conformalReference σ g₁ lam
  let g₁' := dilatedMetric g₁ lam
  let g₂' := dilatedMetric g₂ lam
  let v₁ (a : Fin n) := renormalizedHarmonic (c a) (B a) (u₁ a) lam
  let v₂ (a : Fin n) := renormalizedHarmonic (c a) (B a) (u₂ a) lam
  let V (a : Fin n) (y : (X dim)) := v₂ a y - v₁ a y
  have hT : IsOpen T := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hLT : L ⊆ T := fun y hy => (hS y hy).1
  have hsm₁ : SmoothMetric T g₁' := smoothMetric_dilated hg₁ lam
  have hsm₂ : SmoothMetric T g₂' := smoothMetric_dilated hg₂ lam
  have hγ : SmoothMetric T γ :=
    ⟨fun i j => hσ.contDiffOn.mul (hsm₁.1 i j), fun y hy => (hsm₁.2 y hy).smul (hσpos y)⟩
  have hv₁ (a : Fin n) : ContDiffOn ℝ ∞ (v₁ a) T :=
    contDiffOn_renormalizedHarmonic (hu₁ a).1 (c a) (B a) lam
  have hv₂ (a : Fin n) : ContDiffOn ℝ ∞ (v₂ a) T :=
    contDiffOn_renormalizedHarmonic (hu₂ a).1 (c a) (B a) lam
  have hV (a : Fin n) : ContDiffOn ℝ ∞ (V a) T := (hv₂ a).sub (hv₁ a)
  have hV45 (a : Fin n) (y : (X dim)) (hy : y ∈ L) :
      ‖iteratedFDeriv ℝ (40 + 2 * dim + 1) (V a) y‖ ≤ M := by
    have hfin : ((40 + 2 * dim + 1 : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
    rw [fun_iteratedFDeriv_sub_apply
      (((hv₂ a).contDiffAt (hT.mem_nhds (hLT hy))).of_le hfin)
      (((hv₁ a).contDiffAt (hT.mem_nhds (hLT hy))).of_le hfin)]
    exact (norm_sub_le _ _).trans (add_le_add ((hJ₂ hlam y hy).2 a) ((hJ₁ hlam y hy).2 a))
  have hsmallOnW : EqOn (smallJet γ g₂') 0 (T ∩ {y : (X dim) | lam • y ∈ W}) := by
    apply smallJet_eq_zero_on (hT.inter (hW.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)))
    intro y hy
    exact principal_eq_inv_of_pos_smul (hsm₂.2 y hy.1) (hσpos y)
      (congrArg (fun A : (Mat dim) => σ y • A) (hmatch hy.2))
  have hinit (y : (X dim)) (hy : y ∈ K) : smallJet γ g₂' y ≤ ε * shrinkingRadius R p depth 1 y :=
    ((hS y (hYL (hKY hy))).2.trans hτ₁).trans (mul_le_mul_of_nonneg_left (hmin hy) hε.le)
  have himprove (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1)
      (htemp : ∀ y ∈ K, smallJet γ g₂' y ≤ ε * shrinkingRadius R p depth δ y)
      (y : (X dim)) (hy : y ∈ K) :
      smallJet γ g₂' y ≤ ε / 2 * shrinkingRadius R p depth δ y := by
    let r := shrinkingRadius R p depth δ
    have hfull : Small Y γ g₂' r ε := by
      intro x hx
      refine ⟨?_, hBeta hlam δ hδ x hx⟩
      by_cases hxK : x ∈ K
      · exact htemp x hxK
      · rcases hOff hlam x ⟨hx, hxK⟩ with hw | hd
        · rw [hsmallOnW ⟨hLT (hYL hx), hw⟩]
          exact mul_nonneg hε.le (shrinkingRadius_pos hR hδ.1 p depth x).le
        · have hfloor : R * b ^ p ≤ r x := (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hb.le hd p) hR.le).trans
                (le_shrinkingRadius hR.le hδ.1 p (hb.le.trans hd))
          exact ((hS x (hYL hx)).2.trans hτb).trans
            ((mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ ε / 2)).trans
              (mul_le_mul_of_nonneg_right (by linarith) (shrinkingRadius_pos hR hδ.1 p depth x).le))
    apply half_bound_of_superlinear_or_fixed (shrinkingRadius_pos hR hδ.1 p depth y) hC hε.le hsplit
    · intro hr
      have hρ'y : r y < ρ₀ := hr.trans hρ₀ρ
      have hrI : r y < ρi := hρ'y.trans_le (min_le_left _ _)
      have hr1 : r y ≤ 1 := hρ'y.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hrs₀ : r y ≤ s₀ ^ (20 + dim : ℕ) :=
        hρ'y.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hscale := interpolation_scale_le (dim := dim) (shrinkingRadius_pos hR hδ.1 p depth y).le hs₀.le hrs₀
      obtain ⟨hc, ho, hχ⟩ := hbuffer y hy
      have hQo := (ball_subset_ball hscale).trans ho
      have hQc := (closedBall_subset_closedBall hscale).trans hc
      have hjet (a : Fin n) (d : ℕ) (hd : d ≤ 10) :
          ‖iteratedFDeriv ℝ d (V a) y‖ ≤ Ci' * (r y) ^ (3 / 2 : ℝ) :=
        hinterp T hT (hYL.trans hLT) (V a) χ (hV a) δ hδ.1 y (hKY hy) A M hA hM
          hrI hr1 hQo (hQc.trans hLT) (fun x hx => hχ (ball_subset_ball hscale hx))
          (fun x hx => hV45 a x (hQc hx)) (hMom hlam δ hδ hfull a) d hd
      have hBr : 0 ≤ Ci' * (r y) ^ (3 / 2 : ℝ) :=
        mul_nonneg hCi' (Real.rpow_nonneg (shrinkingRadius_pos hR hδ.1 p depth y).le _)
      exact ((hRec hlam.ne' y hy).2 _ hBr hjet).trans_eq (by simp only [C, r, mul_assoc])
    · intro _
      exact (hS y (hYL (hKY hy))).2.trans hτρ
  have hmatch' : g₁' 0 = g₂' 0 := by simpa only [g₁', g₂', dilatedMetric, smul_zero] using hmatch₀
  obtain ⟨r, hr, hrT, heq⟩ := exists_ball_metric_eq_of_origin_half_improvement hn hT hK
    (hKY.trans (hYL.trans hLT)) h₀K hγ hsm₁ hsm₂
    (harmonicCoordinates_dilated hΩ hg₁ hchart₁ lam) (harmonicCoordinates_dilated hΩ hg₂ hchart₂ lam)
    (fun y _ => ⟨σ y, hσpos y, rfl⟩) hmatch' hR hε (by omega) hKd hdepth₀ hinit himprove
  refine ⟨lam * r, mul_pos hlam hr, ?_, eqOn_ball_of_eqOn_dilated hlam heq⟩
  intro x hx
  have hx' : ‖x‖ < lam * r := by simpa only [mem_ball, dist_zero_right] using hx
  have hy : lam⁻¹ • x ∈ ball (0 : (X dim)) r := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    exact (inv_mul_lt_iff₀ hlam).mpr hx'
  simpa only [T, mem_ofPred_eq, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] using hrT hy

end CalderonN
