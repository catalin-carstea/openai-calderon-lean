module

public import Proof.Manuscript.MovingTrace.PhysicalResidualEnvelopes
public import Proof.Manuscript.MovingTrace.SmoothCollarLift
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000

open CalderonN Set Filter
open scoped ContDiff Topology

namespace CalderonPaper

/-- The lifted residual agrees with the trial equation on the whole
closed ball. Its continuation into the signed exterior stops at one
rescaled depth, where the boundary profile bounds are still uniform. -/
def residualCutIn (s : ℝ) : ℂ := Real.smoothTransition (s+1)

theorem residualCutIn_contDiff : ContDiff ℝ ∞ residualCutIn :=
  Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))

theorem residualCutIn_one {s : ℝ} (hs : 0 ≤ s) : residualCutIn s = 1 := by
  simp [residualCutIn,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s+1)]

theorem residualCutIn_zero {s : ℝ} (hs : s ≤ -1) : residualCutIn s = 0 := by
  simp [residualCutIn,Real.smoothTransition.zero_of_nonpos (by linarith : s+1 ≤ 0)]

theorem residualCutIn_allJet_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, ∀ j ≤ N, ‖iteratedFDeriv ℝ j residualCutIn q‖ ≤ C := by
  have hD (j : Fin (N+1)) : Continuous (fun q => ‖iteratedFDeriv ℝ j.val residualCutIn q‖) :=
    (residualCutIn_contDiff.continuous_iteratedFDeriv (by simp)).norm
  have hB (j : Fin (N+1)) : ∃ C ≥ 0, ∀ q ∈ Icc (-1 : ℝ) 0,
      ‖iteratedFDeriv ℝ j.val residualCutIn q‖ ≤ C := by
    obtain ⟨r,hr⟩ := isCompact_Icc.bddAbove_image (hD j).continuousOn
    exact ⟨max 0 r,le_max_left _ _,fun q hq => (hr ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose C hC hB using hB
  let A := 1 + ∑ j : Fin (N+1), C j
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hC i)
  refine ⟨A,zero_le_one.trans hA,?_⟩
  intro q j hj
  by_cases hq : q ∈ Icc (-1 : ℝ) 0
  · let i : Fin (N+1) := ⟨j,Nat.lt_succ_of_le hj⟩
    exact (hB i q hq).trans ((Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one))
  · by_cases hlo : q < -1
    · have hEq : residualCutIn =ᶠ[𝓝 q] fun _ => (0:ℂ) := by
        filter_upwards [Iio_mem_nhds hlo] with x hx
        exact residualCutIn_zero hx.le
      have h := (Filter.EventuallyEq.iteratedFDeriv ℝ hEq j).eq_of_nhds
      rw [h]
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero,norm_zero] using zero_le_one.trans hA
      | succ j => simp [zero_le_one.trans hA]
    · have hhi : 0 < q := lt_of_not_ge (fun h => hq ⟨le_of_not_gt hlo,h⟩)
      have hEq : residualCutIn =ᶠ[𝓝 q] fun _ => (1:ℂ) := by
        filter_upwards [Ioi_mem_nhds hhi] with x hx
        exact residualCutIn_one hx.le
      have h := (Filter.EventuallyEq.iteratedFDeriv ℝ hEq j).eq_of_nhds
      rw [h]
      cases j with
      | zero => simpa only [norm_iteratedFDeriv_zero,norm_one] using hA
      | succ j => simp [iteratedFDeriv_succ_const,zero_le_one.trans hA]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem SmoothCollarContribution.exteriorCutIn {J : Set (E × ℝ)} (N : ℕ) :
    SmoothCollarContribution J (fun h q => residualCutIn (q.2/h)) N (fun h => h⁻¹^N) := by
  obtain ⟨C,hC,hB⟩ := residualCutIn_allJet_bound N
  have hS (h : ℝ) : ContDiff ℝ ∞ (fun q : E × ℝ => residualCutIn (q.2/h)) :=
    residualCutIn_contDiff.comp (contDiff_snd.div_const h)
  refine ⟨fun q hq h hh hh₁ => (hS h).contDiffAt, C,hC,?_⟩
  intro q hq h hh hh₁ _ j hj
  let L : E × ℝ →L[ℝ] ℝ := h⁻¹ • ContinuousLinearMap.snd ℝ E ℝ
  have hL : ‖L‖ ≤ h⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound L (inv_nonneg.mpr hh.le)
    intro q
    change ‖h⁻¹ • q.2‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le q) (inv_nonneg.mpr hh.le)
  have hEq : (fun q : E × ℝ => residualCutIn (q.2/h)) = residualCutIn ∘ L := by
    funext q
    simp [L,div_eq_mul_inv, mul_comm]
  change ‖iteratedFDeriv ℝ j (fun q : E × ℝ => residualCutIn (q.2/h)) q‖ ≤ C * h⁻¹^N
  rw [hEq,L.iteratedFDeriv_comp_right residualCutIn_contDiff q (by simp : (j : ℕ∞ω) ≤ ∞)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const,Finset.card_fin]
  have hLo : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh₁
  exact mul_le_mul (hB (L q) j hj)
    ((pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_right₀ hLo hj))
    (by positivity) hC

end CalderonPaper
