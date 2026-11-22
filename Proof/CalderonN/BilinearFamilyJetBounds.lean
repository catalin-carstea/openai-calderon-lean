module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum

/-! From BilinearFamilyJetBounds in the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_iteratedFDeriv_bilinear_at_le
    (B : E →L[ℝ] F →L[ℝ] G) (f : P → E) (g : P → F) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖*∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨s,hs,hxs,hfsRaw⟩ := hf.contDiffOn' (m := (n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨t,ht,hxt,hgtRaw⟩ := hg.contDiffOn' (m := (n:ℕ∞ω)) (by simp) (by simp)
  have hfs0 : ContDiffOn ℝ (n:ℕ∞ω) f s := by simpa using hfsRaw
  have hgt0 : ContDiffOn ℝ (n:ℕ∞ω) g t := by simpa using hgtRaw
  have hfs : ContDiffOn ℝ (n:ℕ∞ω) f (s∩t) := hfs0.mono inter_subset_left
  have hgt : ContDiffOn ℝ (n:ℕ∞ω) g (s∩t) := hgt0.mono inter_subset_right
  have hOpen := hs.inter ht
  have hx : x ∈ s∩t := ⟨hxs,hxt⟩
  have hcf (i : ℕ) : iteratedFDerivWithin ℝ i f (s∩t) x = iteratedFDeriv ℝ i f x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hOpen.uniqueDiffOn (hf.of_le (by simp)) hx
  have hcg (i : ℕ) : iteratedFDerivWithin ℝ i g (s∩t) x = iteratedFDeriv ℝ i g x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hOpen.uniqueDiffOn (hg.of_le (by simp)) hx
  have hcb : iteratedFDerivWithin ℝ n (fun y => B (f y) (g y)) (s∩t) x =
      iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hOpen.uniqueDiffOn
      (((B.contDiff.contDiffAt.comp x hf).clm_apply hg).of_le (by simp)) hx
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hfs hgt hOpen.uniqueDiffOn hx (n:=n) le_rfl
  simpa only [hcb,hcf,hcg] using h

/-- A small factor in either input's whole finite jet remains a small factor
    after applying a fixed bilinear operator. -/
theorem norm_iteratedFDeriv_bilinear_common_bound
    (B : E →L[ℝ] F →L[ℝ] G) (f : P → E) (g : P → F) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (N : ℕ) (Cf Cg : ℝ) (hf0 : 0 ≤ Cf) (hg0 : 0 ≤ Cg)
    (hfj : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j f x‖ ≤ Cf)
    (hgj : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j g x‖ ≤ Cg)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤ ‖B‖*2^N*Cf*Cg := by
  apply (norm_iteratedFDeriv_bilinear_at_le B f g x hf hg n).trans
  have hSum : (∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*‖iteratedFDeriv ℝ i f x‖*
      ‖iteratedFDeriv ℝ (n-i) g x‖) ≤ 2^n*Cf*Cg := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*Cf*Cg := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i ≤ N := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hn
        have hniN : n-i ≤ N := (Nat.sub_le _ _).trans hn
        gcongr
        exact hfj i hiN
        exact hgj (n-i) hniN
      _ = 2^n*Cf*Cg := by
        rw [← Finset.sum_mul,← Finset.sum_mul]
        have hChoose : (∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)) = 2^n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [hChoose]
  have hPow : (2:ℝ)^n ≤ 2^N := pow_le_pow_right₀ (by norm_num) hn
  exact (mul_le_mul_of_nonneg_left hSum (norm_nonneg B)).trans
    (by calc
      _ = ‖B‖*(2^n*(Cf*Cg)) := by ring
      _ ≤ ‖B‖*(2^N*(Cf*Cg)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hPow (mul_nonneg hf0 hg0)) (norm_nonneg B)
      _ = _ := by ring)

end ShrinkingSpheres
