module

public import Proof.CalderonN.SoftplusJets
public import Proof.CalderonN.Coercivity
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-! Adapted from `ProfileFrechetJets` in the earlier anisotropic Calderón
formalization, revision d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace CalderonN.SoftplusProfile

variable {dim : ℕ}

lemma norm_iteratedFDeriv_comp_le_of_positive_orders
    (g : ℝ → ℝ) (u : (X dim) → ℝ) (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (n : ℕ) (hn : 1 ≤ n) (x : (X dim)) (C D : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i g (u x)‖ ≤ C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ u) x‖ ≤ (n.factorial : ℝ) * C * D ^ n := by
  let G : ℝ → ℝ := fun s => g s - g (u x)
  have hG : ContDiff ℝ ∞ G := hg.sub contDiff_const
  have hsub (i : ℕ) (hi : 1 ≤ i) :
      iteratedFDeriv ℝ i G (u x) = iteratedFDeriv ℝ i g (u x) := by
    change iteratedFDeriv ℝ i (g - fun _ : ℝ => g (u x)) (u x) = _
    rw [iteratedFDeriv_sub_apply (hg.of_le (by simp)).contDiffAt contDiffAt_const,
      iteratedFDeriv_const_of_ne (by omega)]
    simp
  have hGbound : ∀ i : ℕ, i ≤ n → ‖iteratedFDeriv ℝ i G (u x)‖ ≤ C := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simpa [norm_iteratedFDeriv_zero, G] using hC0
    · rw [hsub i (by omega)]
      exact hC i (by omega) hi
  have h := norm_iteratedFDeriv_comp_le hG hu (by simp) x hGbound hD
  have he : iteratedFDeriv ℝ n (G ∘ u) x = iteratedFDeriv ℝ n (g ∘ u) x := by
    change iteratedFDeriv ℝ n ((g ∘ u) - fun _ : (X dim) => g (u x)) x = _
    rw [iteratedFDeriv_sub_apply ((hg.comp hu).of_le (by simp)).contDiffAt
      contDiffAt_const, iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, sub_zero]
  rwa [he] at h

lemma contDiff_scalar_log_softplus (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun s => Real.log (softplus δ s)) := by
  have he : (fun s => Real.log (softplus δ s)) =
      fun s => Real.log δ + logLogExp (s / δ) :=
    funext (fun s => log_softplus_eq_log_delta_add_logLogExp δ s hδ)
  rw [he]
  exact contDiff_const.add (contDiff_logLogExp.comp (contDiff_id.div_const δ))

def profileJetBoundSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, profileJetBound k

lemma profileJetBoundSum_nonneg (n : ℕ) : 0 ≤ profileJetBoundSum n := by
  exact Finset.sum_nonneg (fun k _ => profileJetBound_nonneg k)

lemma profileJetBound_le_sum (n k : ℕ) (hk : k < n) :
    profileJetBound k ≤ profileJetBoundSum n := by
  exact Finset.single_le_sum (fun i _ => profileJetBound_nonneg i) (Finset.mem_range.mpr hk)

lemma norm_iteratedFDeriv_log_softplus_le (n : ℕ) (hn : 1 ≤ n)
    (δ t : ℝ) (hδ : 0 < δ) :
    ‖iteratedFDeriv ℝ n (fun s => Real.log (softplus δ s)) t‖ ≤
      profileJetBound (n - 1) * logSlope δ t ^ n := by
  have hn' : n - 1 + 1 = n := by omega
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  simpa only [hn'] using abs_iteratedDeriv_log_softplus_le (n - 1) δ t hδ

lemma norm_iteratedFDeriv_log_softplus_comp_le (u : (X dim) → ℝ)
    (hu : ContDiff ℝ ∞ u) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (x : (X dim)) (B D : ℝ) (hB : 1 ≤ B) (hBa : 1 ≤ B * logSlope δ (u x))
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (fun y => Real.log (softplus δ (u y))) x‖ ≤
      (n.factorial : ℝ) * profileJetBoundSum n *
        (B * logSlope δ (u x)) ^ n * D ^ n := by
  have ha := (logSlope_pos δ (u x) hδ).le
  have hC : ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i (fun s => Real.log (softplus δ s)) (u x)‖ ≤
        profileJetBoundSum n * (B * logSlope δ (u x)) ^ n := by
    intro i hi hin
    have hs := norm_iteratedFDeriv_log_softplus_le i hi δ (u x) hδ
    have hterm := profileJetBound_le_sum n (i - 1) (by omega)
    have hp : logSlope δ (u x) ^ i ≤ (B * logSlope δ (u x)) ^ n := by
      have hmul : logSlope δ (u x) ≤ B * logSlope δ (u x) := by nlinarith
      exact (pow_le_pow_left₀ ha hmul i).trans (pow_le_pow_right₀ hBa hin)
    exact hs.trans (mul_le_mul hterm hp (pow_nonneg ha _) (profileJetBoundSum_nonneg n))
  have h := norm_iteratedFDeriv_comp_le_of_positive_orders
    (fun s => Real.log (softplus δ s)) u (contDiff_scalar_log_softplus δ hδ) hu n hn x
    (profileJetBoundSum n * (B * logSlope δ (u x)) ^ n) D (mul_nonneg (profileJetBoundSum_nonneg n) (pow_nonneg (mul_nonneg (by linarith) ha) n)) hC hD
  simpa only [Function.comp_def, mul_assoc] using h

end CalderonN.SoftplusProfile
