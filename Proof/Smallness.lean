import Proof.Geometry
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

noncomputable section
open Set
namespace ShrinkingSpheres

lemma smallJet_nonneg (γ g₂ : MetricField) (y : X) : 0 ≤ smallJet γ g₂ y := by
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  exact Finset.sum_nonneg (fun c hc => Real.sqrt_nonneg _)

/-- Each individual derivative in the finite coordinate budget inherits its common bound. -/
lemma partial_norm_le_smallJet (γ g₂ : MetricField) (y : X) (a b c : ℕ)
    (horder : a+b+c ≤ 8) :
    Real.sqrt (∑ i, ∑ j, (chartPartial a b c
      (fun x => (principal γ g₂ x - (γ x)⁻¹) i j) y)^2) ≤ smallJet γ g₂ y := by
  have ha : a ∈ Finset.range 9 := Finset.mem_range.mpr (by omega)
  have hb : b ∈ Finset.range (9-a) := Finset.mem_range.mpr (by omega)
  have hc : c ∈ Finset.range (9-a-b) := Finset.mem_range.mpr (by omega)
  let T := fun a b c => Real.sqrt (∑ i, ∑ j, (chartPartial a b c
    (fun x => (principal γ g₂ x - (γ x)⁻¹) i j) y)^2)
  calc
    T a b c ≤ ∑ d ∈ Finset.range (9-a-b), T a b d :=
      Finset.single_le_sum (f := fun d => T a b d) (fun d _ => Real.sqrt_nonneg _) hc
    _ ≤ ∑ d ∈ Finset.range (9-a), ∑ e ∈ Finset.range (9-a-d), T a d e :=
      Finset.single_le_sum (f := fun d => ∑ e ∈ Finset.range (9-a-d), T a d e)
        (fun d _ => Finset.sum_nonneg (fun e _ => Real.sqrt_nonneg _)) hb
    _ ≤ smallJet γ g₂ y :=
      Finset.single_le_sum (f := fun d => ∑ e ∈ Finset.range (9-d),
        ∑ f ∈ Finset.range (9-d-e), T d e f)
        (fun d _ => Finset.sum_nonneg (fun e _ => Finset.sum_nonneg
          (fun f _ => Real.sqrt_nonneg _))) ha

lemma partial_component_le_smallJet (γ g₂ : MetricField) (y : X) (a b c : ℕ)
    (horder : a+b+c ≤ 8) (i j : I) :
    |chartPartial a b c (fun x => (principal γ g₂ x - (γ x)⁻¹) i j) y| ≤ smallJet γ g₂ y := by
  let T := fun i j => (chartPartial a b c (fun x => (principal γ g₂ x - (γ x)⁻¹) i j) y)^2
  have hsum : T i j ≤ ∑ i, ∑ j, T i j :=
    (Finset.single_le_sum (f := fun k => T i k) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, T k l)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i))
  exact (Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hsum)).trans
    (partial_norm_le_smallJet γ g₂ y a b c horder)

lemma Small.partial_bound {Y : Set X} {γ g₂ : MetricField} {r : X → ℝ} {ε : ℝ}
    (h : Small Y γ g₂ r ε) {y : X} (hy : y ∈ Y) (a b c : ℕ) (horder : a+b+c ≤ 8) (i j : I) :
    |chartPartial a b c (fun x => (principal γ g₂ x - (γ x)⁻¹) i j) y| ≤ ε * r y :=
  (partial_component_le_smallJet γ g₂ y a b c horder i j).trans (h y hy).1

lemma Small.component_bound {Y : Set X} {γ g₂ : MetricField} {r : X → ℝ} {ε : ℝ}
    (h : Small Y γ g₂ r ε) {y : X} (hy : y ∈ Y) (i j : I) :
    |(principal γ g₂ y - (γ y)⁻¹) i j| ≤ ε * r y :=
  h.partial_bound hy 0 0 0 (by decide) i j

/-- The elementary weighted consequences used by the trace remainders. -/
lemma radius_bounds (r β floor ε : ℝ) (hr : 0 ≤ r) (hf : 1 ≤ floor)
    (hβ : floor ≤ β) (hsmall : r*β^2 ≤ ε) :
    r ≤ ε / floor^2 ∧ r*β ≤ ε/floor ∧ r ≤ ε := by
  have hfpos : 0 < floor := lt_of_lt_of_le zero_lt_one hf
  have hβpos : 0 < β := hfpos.trans_le hβ
  have hsq : floor^2 ≤ β^2 := (sq_le_sq₀ hfpos.le hβpos.le).2 hβ
  have hrf : r*floor^2 ≤ ε := (mul_le_mul_of_nonneg_left hsq hr).trans hsmall
  have hm : r*β*floor ≤ ε := by
    have ht := mul_le_mul_of_nonneg_left hβ (mul_nonneg hr hβpos.le)
    nlinarith
  refine ⟨(le_div_iff₀ (sq_pos_of_pos hfpos)).2 hrf,
    (le_div_iff₀ hfpos).2 hm, ?_⟩
  have hβone : 1 ≤ β^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hβone hr
  linarith

end ShrinkingSpheres
