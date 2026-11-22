module

public import Proof.Manuscript.MovingTrace.ParametricLayerTrace
public import Proof.CalderonN.LocalJetEnvelopeBounds
public import Proof.CalderonN.BilinearFamilyJetBounds
public import Proof.CalderonN.CompactLocalJetBounds
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch.BoundaryLayer Set
open scoped ContDiff

namespace CalderonPaper

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Repeated chain rule at a variable exponent, retaining the value of the
decaying exponential in the bound. -/
theorem norm_iteratedFDeriv_exp_of_jet_bound {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) (D : ℝ) (hD : 1 ≤ D)
    (hJet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => Real.exp (f y)) x‖ ≤
      n.factorial * Real.exp (f x) * D ^ n := by
  apply norm_iteratedFDeriv_comp_at_le f Real.exp x n hf Real.contDiff_exp.contDiffAt
    (Real.exp (f x)) D
  · intro j _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hExp := iteratedDeriv_exp_const_mul j 1
    simp only [one_mul, one_pow] at hExp
    rw [hExp]
    exact Real.norm_of_nonneg (Real.exp_nonneg _) |>.le
  · intro j h₁ hj
    refine (hJet j h₁ hj).trans ?_
    conv_lhs => rw [← pow_one D]
    exact pow_le_pow_right₀ hD h₁

theorem compact_fst_jet_bound {U K : Set E} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {g : E → F} (hg : ContDiffOn ℝ ∞ g U) (N : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ q : E × ℝ, q.1 ∈ K → ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (fun p : E × ℝ => g p.1) q‖ ≤ B := by
  obtain ⟨B,hB,hJet⟩ := exists_uniform_local_finite_jet_bound hK
    (fun p hp => hg.contDiffAt (hU.mem_nhds (hKU hp))) N
  refine ⟨B,hB,?_⟩
  intro q hq n hn
  let L : E × ℝ →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  have hV : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hqV : q ∈ L ⁻¹' U := hKU hq
  have he := L.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hV.uniqueDiffOn hqV
    (by simp : (n : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen n hV hqV, iteratedFDerivWithin_of_isOpen n hU (hKU hq : L q ∈ U)] at he
  change ‖iteratedFDeriv ℝ n (g ∘ L) q‖ ≤ B
  rw [he]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_fin]
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ E ℝ))
    (norm_nonneg _)).trans (by rw [mul_one]; exact hJet q.1 hq n hn)

theorem norm_iteratedFDeriv_normalProjection_le (q : E × ℝ) (hq : -1 ≤ q.2) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun p : E × ℝ => p.2) q‖ ≤ 2 + q.2 := by
  cases n with
  | zero =>
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  | succ n =>
    let L := ContinuousLinearMap.snd ℝ E ℝ
    change ‖iteratedFDeriv ℝ (n + 1) (⇑L) q‖ ≤ _
    rw [← norm_iteratedFDeriv_fderiv]
    have hD : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
    rw [hD]
    cases n with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_snd_le ℝ E ℝ).trans ((by linarith : 1 ≤ 2 + q.2))
    | succ n => simp [iteratedFDeriv_succ_const, show 0 ≤ 2 + q.2 by linarith]

/-- Uniform decay after any prescribed joint geometry and inward-coordinate
jet of the decaying root profile. This estimate retains one half of the
exponential to absorb polynomial factors from the Taylor residual. -/
theorem exists_uniform_exp_profile_joint_jet_bound {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U)
    {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : E × ℝ, q.1 ∈ K → -1 ≤ q.2 → ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (fun p : E × ℝ => Real.exp (-κ p.1 * p.2)) q‖ ≤
        C * Real.exp (-(c / 2) * q.2) := by
  obtain ⟨B,hB,hBJet⟩ := compact_fst_jet_bound hU hK hKU hκ N
  let L := ContinuousLinearMap.mul ℝ ℝ
  let A : ℝ := max 1 (‖L‖ * 2 ^ N * B)
  have hA : 1 ≤ A := le_max_left _ _
  let c' := c / 2
  let C : ℝ := N.factorial * A ^ N * Real.exp B * (Real.exp (2*c') * (N.factorial / c' ^ N))
  have hc' : 0 < c' := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q hq ht j hj
  have hκAt : ContDiffAt ℝ ∞ (fun p : E × ℝ => κ p.1) q :=
    (hκ.contDiffAt (hU.mem_nhds (hKU hq))).comp q contDiff_fst.contDiffAt
  have hκJet (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun p : E × ℝ => -κ p.1) q‖ ≤ B := by
    change ‖iteratedFDeriv ℝ i (-(fun p : E × ℝ => κ p.1)) q‖ ≤ B
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact hBJet q hq i hi
  let f : E × ℝ → ℝ := fun p => -κ p.1 * p.2
  have hfAt : ContDiffAt ℝ ∞ f q := hκAt.neg.mul contDiff_snd.contDiffAt
  have hBound (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i f q‖ ≤ A * (2 + q.2) :=
    (ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound L (fun p : E × ℝ => -κ p.1)
      Prod.snd q hκAt.neg contDiff_snd.contDiffAt N B (2 + q.2)
        (zero_le_one.trans hB) (by linarith) hκJet
        (fun i _ => norm_iteratedFDeriv_normalProjection_le q ht i) i hi).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  have hD : 1 ≤ A * (2 + q.2) := one_le_mul_of_one_le_of_one_le hA (by linarith)
  have hκB : κ q.1 ≤ B := by
    refine (le_abs_self _).trans ?_
    have h := hBJet q hq 0 (Nat.zero_le N)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h
  have he : Real.exp (f q) ≤ Real.exp B * Real.exp (-c * q.2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [f]
    have h := mul_le_mul_of_nonneg_right (show -q.2 ≤ 1 by linarith)
      (sub_nonneg.mpr (hcκ q.1 hq))
    nlinarith
  have hFact : (j.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hj
  have hPow : (A * (2 + q.2)) ^ j ≤ (A * (2 + q.2)) ^ N := pow_le_pow_right₀ hD hj
  have hMoment := pow_mul_exp_neg_mul_le hc' (by linarith : 0 ≤ 2 + q.2) N
  have hMoment' : (2 + q.2) ^ N * Real.exp (-(c / 2) * q.2) ≤
      Real.exp (2*c') * (N.factorial / c' ^ N) := by
    have hExp : Real.exp (2*c') * Real.exp (-c' * (2 + q.2)) = Real.exp (-(c / 2) * q.2) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [c']
      ring
    calc
      _ = Real.exp (2*c') * ((2 + q.2) ^ N * Real.exp (-c' * (2 + q.2))) := by rw [← hExp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hMoment (Real.exp_nonneg _)
  calc
    _ ≤ j.factorial * Real.exp (f q) * (A * (2 + q.2)) ^ j :=
      norm_iteratedFDeriv_exp_of_jet_bound hfAt j _ hD (fun i _ hi => hBound i (hi.trans hj))
    _ ≤ N.factorial * (Real.exp B * Real.exp (-c * q.2)) * (A * (2 + q.2)) ^ N := by gcongr
    _ = (N.factorial * A ^ N * Real.exp B) * ((2 + q.2) ^ N * Real.exp (-(c / 2) * q.2)) *
        Real.exp (-(c / 2) * q.2) := by
      have hExp : Real.exp (-(c / 2) * q.2) * Real.exp (-(c / 2) * q.2) =
          Real.exp (-c * q.2) := by rw [← Real.exp_add]; congr 1 <;> ring
      rw [mul_pow, ← hExp]
      ring
    _ ≤ C * Real.exp (-(c / 2) * q.2) := by
      dsimp [C]
      gcongr

end CalderonPaper
