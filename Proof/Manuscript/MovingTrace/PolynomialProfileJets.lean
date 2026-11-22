module

public import Proof.Manuscript.MovingTrace.ExponentialProfileJets
public import Proof.Manuscript.MovingTrace.ParametricLayerResidualPolynomial
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch.BoundaryLayer Set Polynomial Finset
open scoped ContDiff

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem normalProjection_pow_jet_bound (N m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : E × ℝ, -1 ≤ q.2 → ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (fun p : E × ℝ => p.2 ^ m) q‖ ≤ B * (2 + q.2) ^ m := by
  induction m with
  | zero =>
    refine ⟨1,zero_le_one,?_⟩
    intro q hq j hj
    cases j with
    | zero => simp
    | succ j => simp [iteratedFDeriv_succ_const]
  | succ m ih =>
    obtain ⟨B,hB,hJet⟩ := ih
    let L := ContinuousLinearMap.mul ℝ ℝ
    refine ⟨‖L‖ * 2 ^ N * B, by positivity, ?_⟩
    intro q hq j hj
    have h := ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound L
      (fun p : E × ℝ => p.2 ^ m) Prod.snd q (contDiff_snd.pow m).contDiffAt
      contDiff_snd.contDiffAt N (B * (2 + q.2) ^ m) (2 + q.2) (mul_nonneg hB (pow_nonneg (by linarith) _)) (by linarith)
      (hJet q hq) (fun k _ => norm_iteratedFDeriv_normalProjection_le q hq k) j hj
    simpa only [show (fun p : E × ℝ => L (p.2 ^ m) p.2) = (fun p => p.2 ^ (m + 1)) by
      funext p; exact (pow_succ p.2 m).symm, pow_succ, mul_assoc] using h

private theorem pow_moment_splits_exp {a : ℝ} (ha : 0 < a) (m : ℕ) {s : ℝ} (hs : -1 ≤ s) :
    (2 + s) ^ m * Real.exp (-a * s) ≤
      (Real.exp (2*(a / 2)) * (m.factorial / (a / 2) ^ m)) * Real.exp (-(a / 2) * s) := by
  let b := a / 2
  have hb : 0 < b := by positivity
  have hMoment := pow_mul_exp_neg_mul_le hb (by linarith : 0 ≤ 2 + s) m
  have hExp : Real.exp (2*b) * Real.exp (-b * (2 + s)) * Real.exp (-b * s) = Real.exp (-a * s) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [b]
    ring
  calc
    _ = (Real.exp (2*b) * ((2 + s) ^ m * Real.exp (-b * (2 + s)))) * Real.exp (-b * s) := by
      rw [← hExp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMoment (Real.exp_nonneg _))
      (Real.exp_nonneg _)

/-- Every jet of a polynomial in scaled depth times the decaying root
exponential retains exponential decay, uniformly over compact parameters. -/
theorem exists_uniform_polynomial_profile_joint_jet_bound
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U)
    {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ)
    (hD : ∀ p ∈ U, (P p).natDegree < D) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : E × ℝ, q.1 ∈ K → -1 ≤ q.2 → ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (polynomialProfileFamily κ P) q‖ ≤
        C * Real.exp (-(c / 4) * q.2) := by
  let term (m : ℕ) (q : E × ℝ) : ℂ := (Real.exp (-κ q.1 * q.2) * q.2 ^ m) • (P q.1).coeff m
  obtain ⟨A,hA,hExp⟩ := exists_uniform_exp_profile_joint_jet_bound hU hK hKU hκ hc hcκ N
  have hPow (m : ℕ) := normalProjection_pow_jet_bound (E := E) N m
  choose B hB hPowJet using hPow
  have hCoeff (m : ℕ) := compact_fst_jet_bound hU hK hKU (hP m) N
  choose C hC hCoeffJet using hCoeff
  let L := ContinuousLinearMap.mul ℝ ℝ
  let S : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  let bound (m : ℕ) : ℝ :=
    ‖S‖ * 2 ^ N *
      (‖L‖ * 2 ^ N * A * B m * (Real.exp (2*(c / 4)) * (m.factorial / (c / 4) ^ m))) * C m
  have hBound (m : ℕ) : 0 ≤ bound m := by
    dsimp [bound]
    have hmB := hB m
    have hmC := zero_le_one.trans (hC m)
    positivity
  refine ⟨∑ m ∈ range D, bound m, sum_nonneg (fun m _ => hBound m), ?_⟩
  intro q hq ht j hj
  have hV : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hqV : q ∈ U ×ˢ (univ : Set ℝ) := ⟨hKU hq,mem_univ _⟩
  have hκAt : ContDiffAt ℝ ∞ (fun p : E × ℝ => κ p.1) q :=
    (hκ.contDiffAt (hU.mem_nhds (hKU hq))).comp q contDiff_fst.contDiffAt
  have hExpAt : ContDiffAt ℝ ∞ (fun p : E × ℝ => Real.exp (-κ p.1 * p.2)) q :=
    (hκAt.neg.mul contDiff_snd.contDiffAt).exp
  have hCoeffAt (m : ℕ) : ContDiffAt ℝ ∞ (fun p : E × ℝ => (P p.1).coeff m) q :=
    ((hP m).contDiffAt (hU.mem_nhds (hKU hq))).comp q contDiff_fst.contDiffAt
  have hTermAt (m : ℕ) : ContDiffAt ℝ ∞ (term m) q :=
    (hExpAt.mul (contDiff_snd.pow m).contDiffAt).smul (hCoeffAt m)
  have hEq : EqOn (polynomialProfileFamily κ P) (fun p : E × ℝ => ∑ m ∈ range D, term m p)
      (U ×ˢ (univ : Set ℝ)) := by
    intro p hp
    simp only [term, polynomialProfileFamily, Polynomial.eval_eq_sum_range' (hD p.1 hp.1),
      smul_sum, Complex.real_smul]
    apply sum_congr rfl
    intro m hm
    push_cast
    ring
  rw [← iteratedFDerivWithin_of_isOpen j hV hqV, iteratedFDerivWithin_congr hEq hqV j,
    iteratedFDerivWithin_of_isOpen j hV hqV,
    iteratedFDeriv_fun_sum_apply (fun m _ => (hTermAt m).of_le (by simp))]
  refine (norm_sum_le _ _).trans ?_
  rw [sum_mul]
  apply sum_le_sum
  intro m hm
  have hMoment : (2 + q.2) ^ m * Real.exp (-(c / 2) * q.2) ≤
      (Real.exp (2*(c / 4)) * (m.factorial / (c / 4) ^ m)) * Real.exp (-(c / 4) * q.2) := by
    simpa only [show c / 2 / 2 = c / 4 by ring] using
      pow_moment_splits_exp (by positivity : 0 < c / 2) m ht
  have hMultJet (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i (fun p : E × ℝ => Real.exp (-κ p.1 * p.2) * p.2 ^ m) q‖ ≤
        (‖L‖ * 2 ^ N * A * B m * (Real.exp (2*(c / 4)) * (m.factorial / (c / 4) ^ m))) *
          Real.exp (-(c / 4) * q.2) := by
    have h := ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound L
      (fun p : E × ℝ => Real.exp (-κ p.1 * p.2)) (fun p : E × ℝ => p.2 ^ m) q
      hExpAt (contDiff_snd.pow m).contDiffAt N (A * Real.exp (-(c / 2) * q.2))
      (B m * (2 + q.2) ^ m) (by positivity) (mul_nonneg (hB m) (pow_nonneg (by linarith) _))
      (hExp q hq ht) (hPowJet m q ht) i hi
    refine h.trans ?_
    calc
      _ = (‖L‖ * 2 ^ N * A * B m) * ((2 + q.2) ^ m * Real.exp (-(c / 2) * q.2)) := by ring
      _ ≤ _ := by
        rw [mul_assoc _ (Real.exp _ * _) _]
        exact mul_le_mul_of_nonneg_left hMoment (by have := hB m; positivity)
  have h := ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound S
    (fun p : E × ℝ => Real.exp (-κ p.1 * p.2) * p.2 ^ m) (fun p : E × ℝ => (P p.1).coeff m) q
    (hExpAt.mul (contDiff_snd.pow m).contDiffAt) (hCoeffAt m) N _ (C m)
    (by have := hB m; positivity) (zero_le_one.trans (hC m)) hMultJet (hCoeffJet m q hq) j hj
  refine h.trans_eq ?_
  dsimp [bound]
  ring

end CalderonPaper
