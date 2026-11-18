import Proof.ScalarRotationDataHigherJets
import Proof.NativeScalarHigherEndpoints
import Proof.ZeroOrderRotationHighLiftJets
import Proof.SmoothFiniteJetDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def scalarAngularCoefficientBudget (Q0 : SmoothCoefficientJets 2) : ℝ :=
  1+∑ i : I,∑ j : I,‖closedFourJetAngularDerivativeL Q0 i j‖

lemma scalarAngularCoefficientBudget_bounds (Q0 : SmoothCoefficientJets 2) :
    1 ≤ scalarAngularCoefficientBudget Q0 ∧
      ∀ i j,‖closedFourJetAngularDerivativeL Q0 i j‖ ≤ scalarAngularCoefficientBudget Q0 := by
  have hS : 0 ≤ ∑ i : I,∑ j : I,‖closedFourJetAngularDerivativeL Q0 i j‖ := by positivity
  constructor
  · dsimp only [scalarAngularCoefficientBudget];linarith
  · intro i j
    have hh := (Finset.single_le_sum (fun k _ => norm_nonneg (closedFourJetAngularDerivativeL Q0 i k))
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (closedFourJetAngularDerivativeL Q0 k l)))
        (Finset.mem_univ i))
    dsimp only [scalarAngularCoefficientBudget];linarith

namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma scalarHigherFamily_two_jets
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hCJ : 0 ≤ CJ)
    (Q0 : SmoothCoefficientJets 2) (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 4)
    (BQ : ℝ) (hQ : SmoothFiniteJetBound Q ((y,frameVectorLinear d.frame y),0) 2 BQ)
    (CG : ℝ) (hCG : 0 ≤ CG)
    (hAngular : ∀ i j,SmoothFiniteJetBound
      (normalFrameRelativeAngularDerivative d.γ A.scalarOperatorFamily i j)
      ((y,frameVectorLinear d.frame y),0) 2 (CG*(CJ*(d.radius y)^2))) :
    SmoothFiniteJetBound (A.scalarHigherFamily Q0 Q) ((y,frameVectorLinear d.frame y),0) 2
      (((19+9*Real.sqrt 2)*(4*CJ*(1+CG+scalarAngularCoefficientBudget Q0)*BQ))*(d.radius y)^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let CR := scalarAngularCoefficientBudget Q0
  have hLower : SmoothFiniteJetBound (fun x => closedCoefficientLowerJetsL 3 (Q x)) p 2 BQ :=
    (hQ.clm (closedCoefficientLowerJetsL 3)).weaken
      ((mul_le_mul_of_nonneg_right (norm_closedCoefficientLowerJetsL_le 3) hQ.nonneg).trans_eq (one_mul _))
  have hR (ij : I × I) : SmoothFiniteJetBound
      (fun x => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q x)) p 2 (CR*BQ) :=
    (hQ.clm (closedFourJetAngularDerivativeL Q0 ij.1 ij.2)).weaken
      (mul_le_mul_of_nonneg_right ((scalarAngularCoefficientBudget_bounds Q0).2 ij.1 ij.2) hQ.nonneg)
  have hh := A.scalarHigherFamilyFromRotationData_two_jets hCJ _ _ BQ (CR*BQ) hLower hR CG hCG hAngular
  have hWeak : SmoothFiniteJetBound
      (A.scalarHigherFamilyFromRotationData (fun x => closedCoefficientLowerJetsL 3 (Q x))
        (fun ij x => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q x))) p 2
      (((19+9*Real.sqrt 2)*(4*CJ*(1+CG+scalarAngularCoefficientBudget Q0)*BQ))*(d.radius y)^2) :=
    hh.weaken (le_of_eq (by dsimp only [CR];ring))
  have hFun : A.scalarHigherFamily Q0 Q=
      A.scalarHigherFamilyFromRotationData (fun x => closedCoefficientLowerJetsL 3 (Q x))
        (fun ij x => closedFourJetAngularDerivativeL Q0 ij.1 ij.2 (Q x)) := by
    rfl
  rw [hFun]
  exact hWeak
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
