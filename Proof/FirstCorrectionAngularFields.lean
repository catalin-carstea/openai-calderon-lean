import Proof.CoordinateCombinationAngularFields
import Proof.FirstRadialAngularFieldJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def firstCorrectionAngularPacket (q : X →L[ℝ] ℝ) (c : I → ℝ) (t : ℝ) : CoarseRotationAdjointPacket :=
  ((firstRadialAdjointCoarsePacket q).mulCoordinateCombination c).add
    ((firstRadialAdjointCoarsePacket q).smul t)

def firstCorrectionAngularFields (q : X →L[ℝ] ℝ) (c : I → ℝ) (t : ℝ) : CoarseAngularFields :=
  ((CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket q)).mulCoordinateCombination c).add
    ((CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket q)).smul t)

lemma firstCorrectionAngularFields_ofPacket (q : X →L[ℝ] ℝ) (c : I → ℝ) (t : ℝ) :
    CoarseAngularFields.ofPacket (firstCorrectionAngularPacket q c t)=firstCorrectionAngularFields q c t := rfl

lemma firstCorrectionAngularFields_operator (q : X →L[ℝ] ℝ) (c : I → ℝ) (t : ℝ) :
    (firstCorrectionAngularFields q c t).operator =
      (firstRadialAdjointOperatorMapL q).comp (∑ j : I,c j • coordinateMultiplierSobolevL 1 j)+
        t • firstRadialAdjointOperatorMapL q := by
  change ((CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket q)).mulCoordinateCombination c).operator+
    t • (CoarseAngularFields.ofPacket (firstRadialAdjointCoarsePacket q)).operator = _
  rw [CoarseAngularFields.mulCoordinateCombination_operator]
  rfl

lemma firstCorrectionAngularFields_smoothAt
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q : P → X →L[ℝ] ℝ) (c : I → P → ℝ) (t : P → ℝ) (p : P)
    (hq : ContDiffAt ℝ ∞ q p) (hc : ∀ j,ContDiffAt ℝ ∞ (c j) p) (ht : ContDiffAt ℝ ∞ t p) :
    CoarseAngularFields.SmoothAt (fun x => firstCorrectionAngularFields (q x) (fun j => c j x) (t x)) p :=
  ((firstRadialAdjointFields_smoothAt hq).mulCoordinateCombination hc).add
    (CoarseAngularFields.SmoothAt.scalar ht (firstRadialAdjointFields_smoothAt hq))

def firstCorrectionAngularJetBudget (N : ℕ) (Bq Bc Bt : ℝ) : ℝ :=
  coordinateCombinationJetBudget N (firstRadialAngularFieldJetBudget*Bq)*Bc+
    2^N*Bt*(firstRadialAngularFieldJetBudget*Bq)

lemma firstCorrectionAngularFields_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q : P → X →L[ℝ] ℝ) (c : I → P → ℝ) (t : P → ℝ) (p : P)
    (N : ℕ) (Bq Bc Bt : ℝ)
    (hq : SmoothFiniteJetBound q p N Bq) (hc : ∀ j,SmoothFiniteJetBound (c j) p N Bc)
    (ht : SmoothFiniteJetBound t p N Bt) :
    CoarseAngularFields.JetBound (fun x => firstCorrectionAngularFields (q x) (fun j => c j x) (t x))
      p N (firstCorrectionAngularJetBudget N Bq Bc Bt) :=
  ((firstRadialAdjointFields_jet_bound hq).mulCoordinateCombination hc).add
    (CoarseAngularFields.JetBound.scalar ht (firstRadialAdjointFields_jet_bound hq))

end ShrinkingSpheres
