import Proof.CoarseAngularFieldBudgets
import Proof.CoarseAngularFieldSmoothness
import Proof.CoordinateMultiplierSobolev
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

namespace CoarseAngularFields

def mulCoordinateCombination (P : CoarseAngularFields) (q : I → ℝ) : CoarseAngularFields :=
  sum (fun j : I => (P.mulRight (coordinateScalarRotationData j)).smul (q j))

lemma mulCoordinateCombination_operator (P : CoarseAngularFields) (q : I → ℝ) :
    (P.mulCoordinateCombination q).operator = P.operator.comp (∑ j : I,q j • coordinateMultiplierSobolevL 1 j) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [mulCoordinateCombination,sum,smul,mulRight,coordinateScalarRotationData,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,map_sum,map_smul]
  rfl
end CoarseAngularFields

namespace CoarseRotationAdjointPacket

def mulCoordinateCombination (P : CoarseRotationAdjointPacket) (q : I → ℝ) : CoarseRotationAdjointPacket :=
  sum (fun j : I => (P.mulRight (coordinateScalarRotationData j)).smul (q j))
end CoarseRotationAdjointPacket

lemma CoarseAngularFields.ofPacket_mulCoordinateCombination (P : CoarseRotationAdjointPacket) (q : I → ℝ) :
    ofPacket (P.mulCoordinateCombination q) = (ofPacket P).mulCoordinateCombination q := rfl

def coordinateCombinationJetBudget (N : ℕ) (BP : ℝ) : ℝ :=
  ∑ j : I,2^N*(2*(2^N*BP*(coordinateScalarRotationData j).budget))

lemma coordinateCombinationJetBudget_nonneg (N : ℕ) {BP : ℝ} (hBP : 0 ≤ BP) :
    0 ≤ coordinateCombinationJetBudget N BP := by
  unfold coordinateCombinationJetBudget
  exact Finset.sum_nonneg (fun j hj => by have h := (coordinateScalarRotationData j).budget_nonneg;positivity)

lemma coordinateCombinationJetBudget_mul (N : ℕ) (BP c : ℝ) :
    coordinateCombinationJetBudget N (BP*c) = coordinateCombinationJetBudget N BP*c := by
  unfold coordinateCombinationJetBudget
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma CoarseAngularFields.JetBound.mulCoordinateCombination
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P → CoarseAngularFields} {q : I → P → ℝ} {p : P} {N : ℕ} {BP BQ : ℝ}
    (hf : CoarseAngularFields.JetBound f p N BP)
    (hq : ∀ j,SmoothFiniteJetBound (q j) p N BQ) :
    CoarseAngularFields.JetBound (fun x => (f x).mulCoordinateCombination (fun j => q j x)) p N
      (coordinateCombinationJetBudget N BP*BQ) := by
  have hh := CoarseAngularFields.JetBound.sum
    (fun j x => ((f x).mulRight (coordinateScalarRotationData j)).smul (q j x)) p N
    (fun j => 2^N*BQ*(2*(2^N*BP*(coordinateScalarRotationData j).budget)))
    (fun j => CoarseAngularFields.JetBound.scalar (hq j)
      (hf.mulRight ((coordinateScalarRotationData j).constant_jet_bound p N)))
  have hBudget : (∑ j : I,2^N*BQ*(2*(2^N*BP*(coordinateScalarRotationData j).budget))) =
      coordinateCombinationJetBudget N BP*BQ := by
    unfold coordinateCombinationJetBudget
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hBudget] at hh
  exact hh

lemma CoarseAngularFields.SmoothAt.mulCoordinateCombination
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {f : P → CoarseAngularFields} {q : I → P → ℝ} {p : P}
    (hf : CoarseAngularFields.SmoothAt f p) (hq : ∀ j,ContDiffAt ℝ ∞ (q j) p) :
    CoarseAngularFields.SmoothAt (fun x => (f x).mulCoordinateCombination (fun j => q j x)) p :=
  CoarseAngularFields.SmoothAt.sum _ p (fun j =>
    CoarseAngularFields.SmoothAt.scalar (hq j)
      (hf.mulRight (ScalarRotationMultiplierData.SmoothAt.constant (coordinateScalarRotationData j) p)))
end ShrinkingSpheres
