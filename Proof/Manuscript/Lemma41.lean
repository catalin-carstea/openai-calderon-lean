module

public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.RadiusProfileGeometry
public import Proof.CalderonN.CylinderCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Proof.Manuscript.LogRadiusJetBounds
import Proof.CalderonN.MetricPair
import Proof.CalderonN.SoftplusProfile
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

public section

open Set Filter Metric
open scoped BigOperators ContDiff Topology
open CalderonN

namespace CalderonPaper

/-- Lemma 4.1 for the conformal depth and logarithmic softplus radius of §4.
The fixed choice of conformal depth is made before all radius parameters. -/
theorem lemma41
    {n : ℕ} [NeZero n] (normal : I n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) (h0 : (0 : X n) ∈ Ω)
    {g : MetricField n} (hg : SmoothMetric Ω g) (hg0 : g 0 = 1) :
    ∃ L > 0, ∃ c > 0, ∃ C : ℕ → ℝ,
      let Y := coordinateCylinder normal
      let t := conformalDepth normal L
      let γ := conformalReference (depthScale normal L) g
      let r := fun R p => shrinkingRadius R p t
      (∃ lam₀ > 0,
        (∀ lam ∈ Ioo (0 : ℝ) lam₀, ∀ p : ℕ, 2 ≤ p → ∀ R > 0, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
          let f := fun z => Real.log (r R p δ z)
          let b := beta (γ lam) (r R p δ) y
          c * (p : ℝ) ≤ b ∧
          (∀ v : X n,
            (∑ i, ∑ j, metricHessian (γ lam) f y i j * v i * v j)
              ≤ -c * b * metricPair (γ lam) y v v) ∧
          (∀ j : ℕ, 1 ≤ j → ‖iteratedFDeriv ℝ j f y‖ ≤ C j * b ^ j)) ∧
        (∀ p : ℕ, 2 ≤ p → ∀ ε > 0, ∃ R₀ > 0,
          ∀ R ∈ Ioo (0 : ℝ) R₀, ∀ lam ∈ Ioo (0 : ℝ) lam₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Y,
            r R p δ y * (beta (γ lam) (r R p δ) y) ^ 2 ≤ ε)) ∧
      ∀ p : ℕ, 2 ≤ p → ∀ R > 0,
        (∃ l, ∀ δ ∈ Ioc (0 : ℝ) 1,
          LipschitzOnWith l (fun y => (r R p δ y) ^ (1 / (p : ℝ))) Y) ∧
        (∀ y ∈ Y, StrictMonoOn (fun δ => r R p δ y) (Ioc (0 : ℝ) 1)) ∧
        ∀ y ∈ Y, t y ≤ 0 → Tendsto (fun δ => r R p δ y) (𝓝[>] 0) (𝓝 0) := by
  classical
  let Y := coordinateCylinder normal
  let t := conformalDepth normal 4
  let γ := conformalReference (depthScale normal 4) g
  let r := fun R p => shrinkingRadius R p t
  have hL : 0 < (4 : ℝ) := by norm_num
  have hY : IsCompact Y := isCompact_coordinateCylinder
  have ht : ContDiff ℝ ∞ t := contDiff_conformalDepth 4
  obtain ⟨T, hT⟩ := hY.exists_bound_of_continuousOn ht.continuous.continuousOn
  have hdepth (y : X n) (hy : y ∈ Y) : t y ≤ T := (le_abs_self _).trans (hT y hy)
  obtain ⟨u, M, hu, hM, hcov⟩ :=
    exists_uniform_conformalDepth_covector_bounds (normal := normal) hΩ h0 hY hg hL
  have hstrict := eventually_conformalDepth_strict (normal := normal) hΩ h0 hY hg hg0
  obtain ⟨lo, lam₀, ⟨hlo, hlam₀⟩, hlam⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hcov.and hstrict)
  have hmetric (lam : ℝ) (hl : lam ∈ Ioo (0 : ℝ) lam₀) (y : X n) (hy : y ∈ Y) :=
    (hlam ⟨hlo.trans hl.1, hl.2⟩).1 y hy
  have hess (lam : ℝ) (hl : lam ∈ Ioo (0 : ℝ) lam₀) (y : X n) (hy : y ∈ Y) :=
    (hlam ⟨hlo.trans hl.1, hl.2⟩).2 y hy
  let a₀ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha₀ : 0 < a₀ := by
    dsimp [a₀]
    positivity [SoftplusProfile.log_exp_add_one_pos T]
  let c := min (a₀ * u) M⁻¹
  have hc : 0 < c := lt_min (mul_pos ha₀ hu) (inv_pos.mpr hM)
  choose C hC hCbound using fun j : ℕ =>
    exists_log_radius_jet_bounds ht hY (N := j) hu hdepth
  refine ⟨4, hL, c, hc, C, ⟨lam₀, hlam₀, ?_, ?_⟩, ?_⟩
  · dsimp only
    intro lam hlamSmall p hp R hR δ hδ y hy
    let f := fun z => Real.log (r R p δ z)
    let b := beta (γ lam) (r R p δ) y
    obtain ⟨hyΩ, hlow, hup⟩ := hmetric lam hlamSmall y hy
    have htp : DifferentiableAt ℝ t y := ht.differentiable (by simp) y
    have hβ : (a₀ * u) * (p : ℝ) ≤ b := by
      have hA := SoftplusProfile.logSlope_uniform_lower_bound δ (t y) T hδ.1 hδ.2 (hdepth y hy)
      rw [show b = beta (γ lam) (shrinkingRadius R p t δ) y from rfl,
        beta_shrinkingRadius htp hR hδ.1]
      calc
        _ = (p : ℝ) * a₀ * u := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _))
          hlow hu.le (mul_nonneg (Nat.cast_nonneg _) (SoftplusProfile.logSlope_pos δ _ hδ.1).le)
    have hb : 0 ≤ b := Real.sqrt_nonneg _
    refine ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans hβ, ?_, ?_⟩
    · intro v
      have hgPos : (γ lam y).PosDef :=
        (hg.2 _ hyΩ).smul (depthScale_pos (normal := normal) 4 y)
      have hpair := metricPair_nonneg_of_posDef hgPos v
      have hdepthHess : (∑ i, ∑ j, metricHessian (γ lam) t y i j * v i * v j)
          ≤ -(1 : ℝ) * metricPair (γ lam) y v v := by
        simpa only [neg_one_mul] using (hess lam hlamSmall y hy).2 v
      have hh := log_shrinkingRadius_concave isOpen_univ ht.contDiffOn (mem_univ y)
        hR hδ.1 (c := 1) zero_le_one hM p (γ lam) hup v hpair hdepthHess
      simp only [covJet_two_eq_metricHessian, one_div] at hh
      have hcM : c ≤ M⁻¹ := min_le_right _ _
      have hneg : -(M⁻¹ * b) ≤ -c * b := by
        rw [neg_mul]
        exact neg_le_neg (mul_le_mul_of_nonneg_right hcM hb)
      exact hh.trans (mul_le_mul_of_nonneg_right hneg hpair)
    · intro j hj
      exact hCbound j hy (γ lam) hlow hR hδ ((by omega) : 1 ≤ p) j hj le_rfl
  · dsimp only
    intro p hp ε hε
    let K := (p : ℝ)^2 * M^2 * (Real.log (1 + Real.exp T))^(p - 2)
    have hK : 0 < K := by
      have hp' : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
      dsimp [K]
      positivity [SoftplusProfile.log_exp_add_one_pos T]
    refine ⟨ε / K, div_pos hε hK, ?_⟩
    intro R hR lam hlamSmall δ hδ y hy
    have htp : DifferentiableAt ℝ t y := ht.differentiable (by simp) y
    calc
      _ ≤ R * (p : ℝ)^2 * M^2 * (Real.log (1 + Real.exp T))^(p - 2) :=
        shrinkingRadius_mul_beta_sq_le htp hR.1 hδ.1 hδ.2 (hdepth y hy) hM.le hp (γ lam)
          (hmetric lam hlamSmall y hy).2.2
      _ = R * K := by dsimp only [K]; ring
      _ ≤ ε := (le_div_iff₀ hK).mp hR.2.le
  · dsimp only
    intro p hp R hR
    have hpN : p ≠ 0 := by omega
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpN
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨l, hl⟩ := ht.contDiffOn.exists_lipschitzOnWith (by simp)
        (convex_closedBall (0 : X n) 2) (isCompact_closedBall (0 : X n) 2)
      have htL : LipschitzOnWith l t Y := hl.mono coordinateCylinder_subset_closedBall
      let a := R ^ (1 / (p : ℝ))
      refine ⟨‖a‖₊ * (1 * l), fun δ hδ => ?_⟩
      have hLip := (lipschitzWith_smul (β := ℝ) a).comp_lipschitzOnWith
        ((lipschitzWith_softplus hδ.1.ne').comp_lipschitzOnWith htL)
      convert hLip using 1
      funext y
      change (R * softplus δ (t y) ^ p) ^ (1 / (p : ℝ)) = a * softplus δ (t y)
      rw [Real.mul_rpow hR.le (pow_nonneg (softplus_pos hδ.1 _).le _),
        ← Real.rpow_natCast_mul (softplus_pos hδ.1 _).le, mul_one_div_cancel hpR, Real.rpow_one]
    · intro y hy δ hδ δ' hδ' hlt
      exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀
        (strictMonoOn_softplus_scale (t y) hδ.1 hδ'.1 hlt)
        (softplus_pos hδ.1 _).le hpN) hR
    · intro y hy hty
      have hlim := shrinkingRadius_tendsto_zero R hpN hty
      have hf : 𝓝[Ioc (0 : ℝ) 1] (0 : ℝ) = 𝓝[>] (0 : ℝ) := by
        rw [show Ioc (0 : ℝ) 1 = Iic 1 ∩ Ioi 0 from by ext x; simp [and_comm]]
        exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds zero_lt_one))
      rwa [hf] at hlim

end CalderonPaper
