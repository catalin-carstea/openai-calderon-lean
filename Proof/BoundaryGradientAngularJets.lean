import Proof.CoarseAngularFieldSmoothness
import Proof.ClosedScalarRotationJetBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def gradientAngularBaseBudget (N : ℕ) (D : ℝ) (j : I) : ℝ :=
  (∑ i : I,2*(2^N*(CoarseAngularFields.ofPacket (rotationCoarseAdjointPacket i j)).budget*
    (coordinateScalarRotationData i).budget))+
    2*(2^N*D*(coordinateScalarRotationData j).budget)

def boundaryGradientAngularJetBudget (N : ℕ) (D : ℝ) : ℝ :=
  ∑ j : I,2*(2^N*gradientAngularBaseBudget N D j*closedScalarRotationJetBudget)

lemma gradientAngularBaseBudget_nonneg (N : ℕ) {D : ℝ} (hD : 0 ≤ D) (j : I) :
    0 ≤ gradientAngularBaseBudget N D j := by
  have hR (i : I) := (CoarseAngularFields.ofPacket (rotationCoarseAdjointPacket i j)).budget_nonneg
  have hC (i : I) := (coordinateScalarRotationData i).budget_nonneg
  unfold gradientAngularBaseBudget
  exact add_nonneg (Finset.sum_nonneg (fun i _ => by
    have hRi := hR i
    have hCi := hC i
    positivity)) (by have hCj := hC j;positivity)
lemma boundaryGradientAngularJetBudget_nonneg (N : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ boundaryGradientAngularJetBudget N D := by
  apply Finset.sum_nonneg
  intro j hj
  have hBase := gradientAngularBaseBudget_nonneg N hD j
  have hScalar := closedScalarRotationJetBudget_nonneg
  positivity

lemma CoarseAngularFields.SmoothAt.gradient {F : P → CoarseAngularFields} {p : P}
    (hF : CoarseAngularFields.SmoothAt F p) (Q : I → P → ClosedCoefficientJets 3)
    (hQ : ∀ j,ContDiffAt ℝ ∞ (Q j) p) :
    CoarseAngularFields.SmoothAt (fun x => (F x).gradient (fun j => Q j x)) p := by
  apply CoarseAngularFields.SmoothAt.sum
  intro j
  apply CoarseAngularFields.SmoothAt.mulRight
  · apply CoarseAngularFields.SmoothAt.add
    · apply CoarseAngularFields.SmoothAt.sum
      intro i
      exact ((CoarseAngularFields.SmoothAt.constant _ p).mulRight
        (ScalarRotationMultiplierData.SmoothAt.constant _ p)).const_smul (-1)
    · exact hF.mulRight (ScalarRotationMultiplierData.SmoothAt.constant _ p)
  · exact closedCoefficient_scalar_rotation_smoothAt (hQ j)

lemma CoarseAngularFields.JetBound.gradient {F : P → CoarseAngularFields} {p : P} {N : ℕ} {D B : ℝ}
    (hF : CoarseAngularFields.JetBound F p N D) (Q : I → P → ClosedCoefficientJets 3)
    (hQ : ∀ j,SmoothFiniteJetBound (Q j) p N B) :
    CoarseAngularFields.JetBound (fun x => (F x).gradient (fun j => Q j x)) p N
      (boundaryGradientAngularJetBudget N D*B) := by
  let R (i j : I) : CoarseAngularFields := CoarseAngularFields.ofPacket (rotationCoarseAdjointPacket i j)
  let A (j : I) (x : P) : CoarseAngularFields :=
    (CoarseAngularFields.sum (fun i : I => ((R i j).mulRight (coordinateScalarRotationData i)).smul (-1))).add
      ((F x).mulRight (coordinateScalarRotationData j))
  have hA (j : I) : CoarseAngularFields.JetBound (A j) p N (gradientAngularBaseBudget N D j) := by
    have hRot (i : I) := ((R i j).constant_jet_bound p N).mulRight
      ((coordinateScalarRotationData i).constant_jet_bound p N) |>.const_smul (-1)
    simp only [abs_neg,abs_one,one_mul] at hRot
    exact (CoarseAngularFields.JetBound.sum _ p N _ hRot).add
      (hF.mulRight ((coordinateScalarRotationData j).constant_jet_bound p N))
  have hEach (j : I) := (hA j).mulRight (closedCoefficient_scalar_rotation_jet_bound (hQ j))
  have hAll := CoarseAngularFields.JetBound.sum _ p N _ hEach
  have hBudget : (∑ j : I,2*(2^N*gradientAngularBaseBudget N D j*(closedScalarRotationJetBudget*B))) =
      boundaryGradientAngularJetBudget N D*B := by
    unfold boundaryGradientAngularJetBudget
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hBudget] at hAll
  exact hAll

end ShrinkingSpheres
