module

public import Proof.Manuscript.AnnulusJets
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

namespace CalderonPaper

variable {P E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_smoothAngularCutoff [FiniteDimensional ℝ E] :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0) ∧ (∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨fun ξ => 1 - φ ξ, contDiff_const.sub φ.contDiff, ?_, ?_⟩
  · intro ξ hξ
    change 1 - φ ξ = 0
    rw [φ.one_of_mem_closedBall (by simpa [φ, Metric.mem_closedBall, dist_zero_right] using hξ),
      sub_self]
  · intro ξ hξ
    change 1 - φ ξ = 1
    rw [φ.zero_of_le_dist (by simpa [φ, dist_zero_right] using hξ), sub_zero]

theorem contDiffAt_homogeneousAngularCoefficient
    {b : ℕ → P → E → V} {k : ℕ} {p : P} {ξ : E} (hξ : ξ ≠ 0)
    (hb : ContDiffAt ℝ ∞ (Function.uncurry (b k)) (p, ‖ξ‖⁻¹ • ξ)) :
    ContDiffAt ℝ ∞ (Function.uncurry (homogeneousAngularCoefficient b k)) (p, ξ) := by
  have hnorm : ContDiffAt ℝ ∞ (fun z : P × E => ‖z.2‖) (p, ξ) :=
    contDiffAt_snd.norm ℝ hξ
  have hinv := hnorm.inv (norm_ne_zero_iff.mpr hξ)
  have hscale := hnorm.mul (hinv.pow k)
  have hdir : ContDiffAt ℝ ∞ (fun z : P × E => ‖z.2‖⁻¹ • z.2) (p, ξ) :=
    hinv.smul contDiffAt_snd
  have hc := hb.comp (p, ξ) (contDiffAt_fst.prodMk hdir)
  convert hscale.smul hc using 1
  funext z
  rfl

theorem contDiffAt_cutoffAngularRemainder
    {a : P → E → V} {b : ℕ → P → E → V} {χ : E → ℝ} {N : ℕ} {p : P} {ξ : E}
    (ha : ContDiffAt ℝ ∞ (Function.uncurry a) (p, ξ))
    (hb : ∀ k, ∀ η : E, ‖η‖ = 1 → ContDiffAt ℝ ∞ (Function.uncurry (b k)) (p, η))
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ η, ‖η‖ ≤ 1 → χ η = 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (cutoffAngularRemainder a b χ N)) (p, ξ) := by
  by_cases hξ : ξ = 0
  · apply ha.congr_of_eventuallyEq
    have hnear : ∀ᶠ z : P × E in 𝓝 (p, ξ), ‖z.2‖ < 1 :=
      (continuous_norm.comp continuous_snd).continuousAt.eventually (eventually_lt_nhds (by
        change ‖ξ‖ < 1
        simp [hξ]))
    filter_upwards [hnear] with z hz
    change a z.1 z.2 - χ z.2 • _ = a z.1 z.2
    rw [hχ0 _ hz.le, zero_smul, sub_zero]
  · have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hunit : ‖(‖ξ‖⁻¹ : ℝ) • ξ‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hξ0), inv_mul_cancel₀ hξ0.ne']
    have hsum : ContDiffAt ℝ ∞ (fun z : P × E =>
        ∑ k ∈ Finset.range N, homogeneousAngularCoefficient b k z.1 z.2) (p, ξ) :=
      ContDiffAt.sum fun k _ => contDiffAt_homogeneousAngularCoefficient hξ (hb k _ hunit)
    exact ha.sub ((hχ.contDiffAt.comp (p, ξ) contDiffAt_snd).smul hsum)

private theorem rpow_le_shifted_rpow {r : ℝ} (hr : 1 ≤ r) (s : ℝ) :
    r ^ s ≤ (2 : ℝ) ^ |s| * (1 + r) ^ s := by
  have hr0 : 0 < r := by linarith
  have hshift : 0 < 1 + r := by positivity
  by_cases hs : 0 ≤ s
  · have hscale : 1 ≤ (2 : ℝ) ^ |s| :=
      Real.one_le_rpow (by norm_num) (abs_nonneg s)
    apply (Real.rpow_le_rpow hr0.le (show r ≤ 1 + r by linarith) hs).trans
    conv_lhs => rw [← one_mul ((1 + r) ^ s)]
    exact mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hshift.le _)
  · have hs' : s ≤ 0 := (lt_of_not_ge hs).le
    have hboth := Real.rpow_le_rpow_of_nonpos hshift (show 1 + r ≤ 2 * r by linarith) hs'
    rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) hr0.le] at hboth
    have h₂ : 0 < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
    have hm := mul_le_mul_of_nonneg_left hboth h₂.le
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), neg_add_cancel,
      Real.rpow_zero, one_mul] at hm
    simpa only [abs_of_nonpos hs'] using hm

/-- Rapid estimates for every normalized truncation imply all symbol
seminorms for the corresponding classical expansion on a compact parameter set. -/
theorem classicalAngularExpansion_on_compact [FiniteDimensional ℝ E]
    (a : P → E → V) (b : ℕ → P → E → V) {U K : Set P}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (ha : ∀ p ∈ U, ∀ ξ, ContDiffAt ℝ ∞ (Function.uncurry a) (p, ξ))
    (hb : ∀ p ∈ U, ∀ k, ∀ η : E, ‖η‖ = 1 → ContDiffAt ℝ ∞ (Function.uncurry (b k)) (p, η))
    (hpoint : ∀ p ∈ U, ∀ η : E, (1 / 2 : ℝ) ≤ ‖η‖ → ‖η‖ ≤ 2 →
      ∀ N, ∃ C : ℝ, ∀ h ∈ Ioc (0 : ℝ) 1,
        ‖normalizedAnnulusRemainder a b N h p η‖ ≤ C * h ^ N)
    (hjets : ∀ N j l : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K,
      ∀ h ∈ Ioc (0 : ℝ) 1, ∀ η : E, ‖η‖ = 1 →
      ‖angularMixedJet j l (normalizedAnnulusRemainder a b N h) p η‖ ≤ C * h ^ N) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0) ∧ (∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1) ∧
      (∀ k, ∀ p ∈ U, ∀ ξ : E, ξ ≠ 0 →
        ContDiffAt ℝ ∞ (Function.uncurry (homogeneousAngularCoefficient b k)) (p, ξ)) ∧
      (∀ k (p : P) (ξ : E) {r : ℝ}, 0 < r →
        homogeneousAngularCoefficient b k p (r • ξ) =
          (r ^ ((1 : ℝ) - k)) • homogeneousAngularCoefficient b k p ξ) ∧
      ∀ N j l : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ ξ : E,
        ‖angularMixedJet j l (cutoffAngularRemainder a b χ N) p ξ‖ ≤
          C * (1 + ‖ξ‖) ^ ((1 : ℝ) - N - l) := by
  obtain ⟨χ, hχ, hχ0, hχ1⟩ := exists_smoothAngularCutoff (E := E)
  refine ⟨χ, hχ, hχ0, hχ1, ?_, ?_, ?_⟩
  · intro k p hp ξ hξ
    apply contDiffAt_homogeneousAngularCoefficient hξ
    apply hb p hp k
    have hr := norm_pos_iff.mpr hξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
  · intro k p ξ r hr
    rw [homogeneousAngularCoefficient_smul _ _ _ _ _ hr, angularSymbolScale_eq_rpow _ hr]
  · intro N j l
    let s : ℝ := 1 - N - l
    let Q := angularMixedJet j l (cutoffAngularRemainder a b χ N)
    let ratio (z : P × E) := ‖Q z.1 z.2‖ / (1 + ‖z.2‖) ^ s
    have hratio : ContinuousOn ratio (K ×ˢ Metric.closedBall (0 : E) 2) := by
      intro z hz
      have hR := contDiffAt_cutoffAngularRemainder (N := N) (ha _ (hKU hz.1) z.2)
        (hb _ (hKU hz.1)) hχ hχ0
      have hQ := (contDiffAt_angularMixedJet hR j l).continuousAt.norm
      have hpos : 0 < 1 + ‖z.2‖ := by positivity
      have hshift : Continuous (fun w : P × E => 1 + ‖w.2‖) :=
        continuous_const.add (continuous_norm.comp continuous_snd)
      have hw := hshift.continuousAt.rpow_const (p := s) (Or.inl hpos.ne')
      exact (hQ.div hw (Real.rpow_pos_of_pos hpos _).ne').continuousWithinAt
    obtain ⟨B, hB⟩ := (hK.prod (isCompact_closedBall (0 : E) 2)).bddAbove_image hratio
    obtain ⟨C, hC, hCjet⟩ := hjets N j l
    let D := max 1 (max B (C * (2 : ℝ) ^ |s|))
    refine ⟨D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro p hp ξ
    have hξpos : 0 < 1 + ‖ξ‖ := by positivity
    have hweight : 0 < (1 + ‖ξ‖) ^ s := Real.rpow_pos_of_pos hξpos _
    by_cases hξ : ‖ξ‖ ≤ 2
    · have hmem : (p, ξ) ∈ K ×ˢ Metric.closedBall (0 : E) 2 :=
        ⟨hp, by simpa [Metric.mem_closedBall, dist_zero_right] using hξ⟩
      have hratio_le : ratio (p, ξ) ≤ D :=
        (hB (mem_image_of_mem ratio hmem)).trans ((le_max_left _ _).trans (le_max_right _ _))
      exact (div_le_iff₀ hweight).mp hratio_le
    · have hh : 2 < ‖ξ‖ := lt_of_not_ge hξ
      have hhom (q : P) (hq : q ∈ U) (η : E) (hlo : (1 / 2 : ℝ) ≤ ‖η‖)
          (hhi : ‖η‖ ≤ 2) (k : ℕ) :=
        coefficients_eq_homogeneous_of_annulus a b q (hpoint q hq) η hlo hhi k
      have hhigh :=
        angularMixedJet_cutoffAngularRemainder_bound a b χ hU (hKU hp) ξ hh hχ1
          hhom N j l C (hCjet p hp)
      calc
        ‖Q p ξ‖ ≤ C * ‖ξ‖ ^ s := hhigh
        _ ≤ C * ((2 : ℝ) ^ |s| * (1 + ‖ξ‖) ^ s) :=
          mul_le_mul_of_nonneg_left (rpow_le_shifted_rpow (by linarith) s) hC.le
        _ ≤ D * (1 + ‖ξ‖) ^ s := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hweight.le

end CalderonPaper
