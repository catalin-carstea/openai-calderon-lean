module

public import Proof.Manuscript.MovingTrace.UniformAngularResidualCorrection
public import Proof.CalderonN.MixedSliceJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 2900000

open CalderonN Set Metric
open scoped ContDiff

namespace CalderonPaper

variable {P E Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def normalJetReadout (w : E → Z) (D : P × E → Z [×1]→L[ℝ] ℝ) (q : P × E) : ℝ :=
  (continuousMultilinearCurryFin1 ℝ Z ℝ (D q)) (w q.2)

theorem normalJetReadout_contDiffOn {T : Set (P × E)} {w : E → Z}
    (hw : ContDiff ℝ ∞ w) {D : P × E → Z [×1]→L[ℝ] ℝ}
    (hD : ContDiffOn ℝ ∞ D T) :
    ContDiffOn ℝ ∞ (normalJetReadout w D) T := by
  let L := (continuousMultilinearCurryFin1 ℝ Z ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  exact (L.contDiff.comp_contDiffOn hD).clm_apply (hw.comp contDiff_snd).contDiffOn

theorem norm_normalJetReadout_on_compact {T : Set (P × E)} (hT : IsOpen T)
    {K : Set E} (hK : IsCompact K) (w : E → Z) (hw : ContDiff ℝ ∞ w) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : P × E → Z [×1]→L[ℝ] ℝ)
      (hD : ContDiffOn ℝ ∞ D T) (p : P) (x : E), x ∈ K → (p,x) ∈ T →
      ∀ M : ℝ, 0 ≤ M → (∀ j ≤ N, ‖iteratedFDeriv ℝ j D (p,x)‖ ≤ M) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (normalJetReadout w D) (p,x)‖ ≤ C*M := by
  have hU (j : Fin (N+1)) : ∃ A ≥ 0, ∀ x ∈ K, ‖iteratedFDeriv ℝ j.val w x‖ ≤ A := by
    obtain ⟨A,hA⟩ := hK.bddAbove_image
      ((hw.continuous_iteratedFDeriv (m := j.val) (by simp : (j.val : ℕ∞ω) ≤ ∞)).norm.continuousOn)
    exact ⟨max 0 A,le_max_left _ _,fun x hx => (hA ⟨x,hx,rfl⟩).trans (le_max_right _ _)⟩
  choose A hA hW using hU
  let B := ∑ i : Fin (N+1), A i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hA i)
  let S := ContinuousLinearMap.snd ℝ P E
  have hS : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound S zero_le_one (by
    intro q
    change ‖q.2‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_snd_le q)
  let L := (continuousMultilinearCurryFin1 ℝ Z ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (by
    intro q
    change ‖continuousMultilinearCurryFin1 ℝ Z ℝ q‖ ≤ 1 * ‖q‖
    rw [LinearIsometryEquiv.norm_map,one_mul])
  refine ⟨(2:ℝ)^N*B,by positivity,?_⟩
  intro D hD p x hx hq M hM hDjet j hj
  let q := (p,x)
  have hZ (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i (w ∘ S) q‖ ≤ B := by
    let k : Fin (N+1) := ⟨i,Nat.lt_succ_of_le hi⟩
    rw [S.iteratedFDeriv_comp_right hw q (by simp : (i:ℕ∞ω) ≤ ∞)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const,Finset.card_fin]
    change ‖iteratedFDeriv ℝ i w x‖ * ‖S‖^i ≤ B
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hS)).trans
      ((hW k x hx).trans (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_univ k)))
  have hF (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i (L ∘ D) q‖ ≤ M := by
    exact ((L.norm_iteratedFDeriv_comp_left (hD.contDiffAt (hT.mem_nhds hq)) (by simp)).trans
      (mul_le_of_le_one_left (norm_nonneg _) hL)).trans (hDjet i hi)
  change ‖iteratedFDeriv ℝ j (fun q => (L ∘ D) q ((w ∘ S) q)) q‖ ≤ _
  rw [← iteratedFDerivWithin_of_isOpen j hT hq]
  refine (norm_iteratedFDerivWithin_clm_apply (L.contDiff.comp_contDiffOn hD)
    (hw.comp_continuousLinearMap (g := S)).contDiffOn hT.uniqueDiffOn hq (by simp)).trans ?_
  simp only [iteratedFDerivWithin_of_isOpen _ hT hq]
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * M * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF i (Nat.le_of_lt_succ (Finset.mem_range.mp hi) |>.trans hj))
        (by positivity)) (hZ (j-i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^j*B*M := by
      rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow]
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hM

theorem normalJetReadout_iteratedFDeriv (w : E → Z) (b : P → Z → ℝ) (q : P × E) :
    normalJetReadout w (fun r => iteratedFDeriv ℝ 1 (b r.1) (w r.2)) q =
      fderiv ℝ (b q.1) (w q.2) (w q.2) := by
  change iteratedFDeriv ℝ 1 (b q.1) (w q.2) (fun _ => w q.2) = _
  rw [iteratedFDeriv_one_apply]

end CalderonPaper
