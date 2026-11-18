import Proof.FourthDerivativeProductBounds
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The higher chain-rule bound is local in both functions and their jets. -/
lemma norm_iteratedFDeriv_comp_at_le (f : P → Q) (g : Q → E) (x : P) (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (C D : ℝ)
    (hC : ∀ i,i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i,1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial*C*D^n := by
  obtain ⟨u,hu,hfu⟩ := hf.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨v,hv,hgv⟩ := hg.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨U,hUu,hU,hxU⟩ := mem_nhds_iff.mp hu
  obtain ⟨V,hVv,hV,hfxV⟩ := mem_nhds_iff.mp hv
  obtain ⟨W,hWpre,hW,hxW⟩ := mem_nhds_iff.mp (hf.continuousAt.preimage_mem_nhds (hV.mem_nhds hfxV))
  let S := U ∩ W
  have hS : IsOpen S := hU.inter hW
  have hxS : x ∈ S := ⟨hxU,hxW⟩
  have hb := norm_iteratedFDerivWithin_comp_le (hgv.mono hVv)
    (hfu.mono (fun y hy => hUu hy.1)) (show n ≤ (n:ℕ∞ω) from le_rfl)
    hV.uniqueDiffOn hS.uniqueDiffOn (fun y hy => hWpre hy.2) hxS
    (C:=C) (D:=D)
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen i hV hfxV];exact hC i hi)
    (fun i hi hin => by rw [iteratedFDerivWithin_of_isOpen i hS hxS];exact hD i hi hin)
  rwa [iteratedFDerivWithin_of_isOpen n hS hxS] at hb

/-- Common pointwise jet envelopes multiply with a binomial factor. -/
lemma norm_iteratedFDeriv_mul_envelope_at (f g : P → ℝ) (x : P) (n : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (A B : ℝ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hF : ∀ i,i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hG : ∀ i,i ≤ n → ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤ (2:ℝ)^n*A*B := by
  obtain ⟨u,hu,hfu⟩ := hf.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨v,hv,hgv⟩ := hg.contDiffOn (m:=(n:ℕ∞ω)) (by simp) (by simp)
  obtain ⟨U,hUu,hU,hxU⟩ := mem_nhds_iff.mp hu
  obtain ⟨V,hVv,hV,hxV⟩ := mem_nhds_iff.mp hv
  let S := U ∩ V
  have hS : IsOpen S := hU.inter hV
  have hxS : x ∈ S := ⟨hxU,hxV⟩
  have hb := norm_iteratedFDerivWithin_mul_le (hfu.mono (fun y hy => hUu hy.1))
    (hgv.mono (fun y hy => hVv hy.2)) hS.uniqueDiffOn hxS (n:=n) (N:=(n:ℕ∞ω)) le_rfl
  have hEq (h : P → ℝ) (i : ℕ) : iteratedFDerivWithin ℝ i h S x = iteratedFDeriv ℝ i h x :=
    iteratedFDerivWithin_of_isOpen i hS hxS
  simp only [hEq] at hb
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)*A*B := Finset.sum_le_sum (fun i hi => ?_)
    _ = (2:ℝ)^n*A*B := ?_
  · have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hF i hin) (by positivity))
      (hG (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
  · have hSum : (∑ i ∈ Finset.range (n+1),(n.choose i:ℝ)) = (2:ℝ)^n := by
      exact_mod_cast Nat.sum_range_choose n
    rw [← Finset.sum_mul,← Finset.sum_mul,hSum]

lemma norm_iteratedFDeriv_comp_three_envelope (f : P → Q) (g : Q → E) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hG : ∀ i,i ≤ 3 → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hF : ∀ i,1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ D) :
    ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ 6*C*D^3 := by
  intro n hn
  have hPow (i : ℕ) (hi : 1 ≤ i) : D ≤ D^i := by
    simpa only [pow_one] using pow_le_pow_right₀ hD hi
  have hb := norm_iteratedFDeriv_comp_at_le f g x n hf hg C D
    (fun i hi => hG i (hi.trans hn))
    (fun i hi hin => (hF i hi (hin.trans hn)).trans (hPow i hi))
  have hFact : (n.factorial:ℝ) ≤ 6 := by interval_cases n <;> norm_num
  have hPn : D^n ≤ D^3 := pow_le_pow_right₀ hD hn
  exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_right hFact hC) hPn (by positivity) (by positivity))

end ShrinkingSpheres
