import Proof.CoordinateCombinationAngularFields
import Proof.CoarseAngularScaledJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres

def firstErrorAngularJetBudget (BR BP BQ BL BG : ℝ) : ℝ :=
  2^3*BR*coordinateCombinationJetBudget 3 BP*BQ+2^3*BL*BP+BG

lemma firstErrorAngularJetBudget_nonneg (BR BP BQ BL BG : ℝ)
    (hBR : 0 ≤ BR) (hBP : 0 ≤ BP) (hBQ : 0 ≤ BQ) (hBL : 0 ≤ BL) (hBG : 0 ≤ BG) :
    0 ≤ firstErrorAngularJetBudget BR BP BQ BL BG := by
  have hC := coordinateCombinationJetBudget_nonneg 3 hBP
  unfold firstErrorAngularJetBudget
  positivity

lemma firstError_angular_scaled_three_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A G : P → CoarseAngularFields} {q : I → P → ℝ} {R b : P → ℝ} {p : P}
    {r β c BR BP BQ BL BG : ℝ} (hr : 0 < r) (hβ : 1 ≤ β) (hrβ : r*β ≤ 1)
    (hc : 0 ≤ c) (hBR : 0 ≤ BR) (hBP : 0 ≤ BP) (hBQ : 0 ≤ BQ) (hBL : 0 ≤ BL) (hBG : 0 ≤ BG)
    (hA : CoarseAngularFields.JetBound A p 3 (BP*r^2))
    (hq : ∀ j,SmoothFiniteJetBound (q j) p 3 (BQ*c))
    (hR : SmoothFiniteJetBound R p 3 BR) (hb : SmoothFiniteJetBound b p 3 (BL*c))
    (hG : CoarseAngularFields.JetBound G p 3 (BG*c*r)) :
    CoarseAngularFields.JetBound (fun x =>
      (((((A x).mulCoordinateCombination (fun j => q j x)).smul (R x)).smul r⁻¹).add
        ((A x).smul (β*b x))).add (G x)) p 3 (firstErrorAngularJetBudget BR BP BQ BL BG*c*r) := by
  have hCombo := hA.mulCoordinateCombination hq
  rw [coordinateCombinationJetBudget_mul] at hCombo
  have hComboBudget : coordinateCombinationJetBudget 3 BP*r^2*(BQ*c) =
      (coordinateCombinationJetBudget 3 BP*BQ*c)*r^2 := by ring
  rw [hComboBudget] at hCombo
  have hFirst := CoarseAngularFields.JetBound.scalar hR hCombo
  have hFirstBudget : 2^3*BR*((coordinateCombinationJetBudget 3 BP*BQ*c)*r^2) =
      (2^3*BR*coordinateCombinationJetBudget 3 BP*BQ*c)*r^2 := by ring
  rw [hFirstBudget] at hFirst
  have hFirst' := hFirst.radius_rescale hr
  have hBetaA := hA.const_smul β
  rw [abs_of_pos (zero_lt_one.trans_le hβ)] at hBetaA
  have hGain : β*r^2 ≤ r := by nlinarith only [mul_le_mul_of_nonneg_left hrβ hr.le]
  have hBetaA' := hBetaA.weaken (show β*(BP*r^2) ≤ BP*r by nlinarith only [mul_le_mul_of_nonneg_left hGain hBP])
  have hSecond := CoarseAngularFields.JetBound.scalar hb hBetaA'
  have hSecondBudget : 2^3*(BL*c)*(BP*r) = (2^3*BL*BP)*c*r := by ring
  rw [hSecondBudget] at hSecond
  have hSum := (hFirst'.add hSecond).add hG
  have hBudget : (2^3*BR*coordinateCombinationJetBudget 3 BP*BQ*c)*r+(2^3*BL*BP)*c*r+BG*c*r =
      firstErrorAngularJetBudget BR BP BQ BL BG*c*r := by unfold firstErrorAngularJetBudget;ring
  rw [hBudget] at hSum
  simpa only [CoarseAngularFields.add,CoarseAngularFields.smul,smul_smul,mul_comm] using hSum
end ShrinkingSpheres
