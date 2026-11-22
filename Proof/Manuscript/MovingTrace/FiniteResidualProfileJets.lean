module

public import Proof.Manuscript.MovingTrace.ScaledNormalProfileJets
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000

open CalderonPaper Set Polynomial Finset
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} (B : ParametricLayerCoefficients (n := n) U)

/-- All joint derivatives of the residual of the Taylor polynomial part of
the collar operator retain the transport cancellation. The depth scaling
costs at most h to the negative number of requested derivatives. -/
theorem finiteResidualProfile_scaled_jet_bound
    (hU : IsOpen U) {K J : Set E} (hK : IsClosed K) (hJ : IsCompact J) (hJU : J ⊆ U)
    (a : E → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (M N : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (h : ℝ), 0 < h → h ≤ 1 →
      ∀ q : E × ℝ, q.1 ∈ J → -1 ≤ q.2 / h → ∀ j ≤ N,
        ‖iteratedFDeriv ℝ j (fun p : E × ℝ => B.finiteResidualProfile a M h (p.1,p.2/h)) q‖ ≤
          C * h ^ (M + 1) * h⁻¹ ^ N * Real.exp (-c * (q.2 / h)) := by
  let I := Fin (2 * M + 3)
  let profile (i : I) : E × ℝ → ℂ := polynomialProfileFamily B.kappa
    (fun p => (B.finiteResidualPolynomial a M p).coeff i.val)
  have hCoeff (i : I) := B.finiteResidualPolynomial_coeff_regular hU hK a ha ha0 M i.val
  have hDegree (i : I) (p : E) (hp : p ∈ U) :
      ((B.finiteResidualPolynomial a M p).coeff i.val).natDegree < 4 * M + 4 :=
    Nat.lt_succ_of_le (B.finiteResidualPolynomial_coeff_degree hU hK a ha ha0 M i.val hp)
  have hProfile (i : I) : ContDiffOn ℝ ∞ (profile i) (U ×ˢ (univ : Set ℝ)) :=
    (hCoeff i).profile B.kappa_smooth _ (hDegree i)
  obtain ⟨c,hc,hcκ⟩ := exists_positive_lower_bound_on_compact hJ
    (B.kappa_smooth.continuousOn.mono hJU) (fun p hp => B.kappa_pos p (hJU hp))
  have hBounds (i : I) := exists_uniform_polynomial_profile_joint_jet_bound hU hJ hJU
    B.kappa_smooth hc hcκ (hCoeff i) (4 * M + 4) (hDegree i) N
  choose C hC hJets using hBounds
  let C' := ∑ i : I, C i
  have hC' : 0 ≤ C' := sum_nonneg (fun i _ => hC i)
  refine ⟨c/4,C',by positivity,hC',?_⟩
  intro h hh hh₁ q hq ht j hj
  let V : Set (E × ℝ) := U ×ˢ univ
  have hV : IsOpen V := hU.prod isOpen_univ
  have hqV : q ∈ V := ⟨hJU hq,mem_univ _⟩
  let L : (E × ℝ) →L[ℝ] E × ℝ := scaleNormal h
  have hImage : MapsTo L V V := fun p hp => ⟨hp.1,mem_univ _⟩
  let F (i : I) (p : E × ℝ) : ℂ :=
    if M < i.val then ((h : ℂ) ^ i.val) • profile i (L p) else 0
  have hEq : EqOn (fun p : E × ℝ => B.finiteResidualProfile a M h (p.1,p.2/h))
      (fun p : E × ℝ => ∑ i : I, F i p) V := by
    intro p hp
    unfold finiteResidualProfile
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpos : M < i.val
    · simp [F, hpos, profile, L, scaleNormal_apply, polynomialProfileFamily, polynomialProfile]
    · rw [B.finiteResidualPolynomial_coeff_zero hU hK a ha ha0 M i.val (Nat.le_of_not_lt hpos) hp.1]
      simp [F, hpos, polynomialProfile]
  have hProfileAt (i : I) : ContDiffAt ℝ ∞ (profile i ∘ L) q :=
    ((hProfile i).comp L.contDiff.contDiffOn hImage).contDiffAt (hV.mem_nhds hqV)
  have hFAt (i : I) : ContDiffAt ℝ ∞ (F i) q := by
    by_cases hpos : M < i.val
    · simpa [F,hpos,Function.comp_def] using (hProfileAt i).const_smul ((h : ℂ) ^ i.val)
    · simpa [F,hpos] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E × ℝ => (0:ℂ)) q)
  rw [← iteratedFDerivWithin_of_isOpen j hV hqV, iteratedFDerivWithin_congr hEq hqV j,
    iteratedFDerivWithin_of_isOpen j hV hqV,
    iteratedFDeriv_fun_sum_apply (fun i _ => (hFAt i).of_le (by simp))]
  refine (norm_sum_le _ _).trans ?_
  dsimp [C']
  rw [sum_mul,sum_mul,sum_mul]
  apply sum_le_sum
  intro i hi
  by_cases hpos : M < i.val
  · have hS : ‖iteratedFDeriv ℝ j (profile i ∘ L) q‖ ≤
        (C i * Real.exp (-(c / 4) * (q.2 / h))) * h⁻¹ ^ N := by
      have hComp : (profile i ∘ L) = fun p : E × ℝ => profile i (p.1,p.2/h) := by
        funext p
        exact congrArg (profile i) (scaleNormal_apply h p)
      rw [hComp]
      refine (norm_iteratedFDeriv_scaleNormal_le hh hh₁ hU (hProfile i) q hqV.1 j).trans ?_
      have hJ' : ‖iteratedFDeriv ℝ j (profile i) (q.1,q.2/h)‖ ≤
          C i * Real.exp (-(c / 4) * (q.2/h)) :=
        hJets i (q.1,q.2/h) hq ht j hj
      have hInv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh₁
      exact mul_le_mul hJ' (pow_le_pow_right₀ hInv hj)
        (pow_nonneg (inv_nonneg.mpr hh.le) _) (mul_nonneg (hC i) (Real.exp_nonneg _))
    have hPow : h ^ i.val ≤ h ^ (M + 1) :=
      pow_le_pow_of_le_one hh.le hh₁ (Nat.succ_le_of_lt hpos)
    have hFun : F i = ((h : ℂ) ^ i.val) • (profile i ∘ L) := by
      funext p
      exact ite_eq_left hpos
    have hDiff : ContDiffAt ℝ j (profile i ∘ L) q := (hProfileAt i).of_le (by simp)
    rw [hFun,iteratedFDeriv_const_smul_apply hDiff,norm_smul,norm_pow,
      Complex.norm_real,Real.norm_of_nonneg hh.le]
    calc
      _ ≤ h ^ (M + 1) * ((C i * Real.exp (-(c / 4) * (q.2/h))) * h⁻¹ ^ N) :=
        mul_le_mul hPow hS (norm_nonneg _) (pow_nonneg hh.le _)
      _ = _ := by ring
  · have hZero : F i = 0 := by
      funext p
      exact ite_eq_right hpos
    rw [hZero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    have hCi := hC i
    positivity

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
