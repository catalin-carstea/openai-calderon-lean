import Proof.ScalarRotationDataHigherEndpoints
import Proof.ZeroOrderRotationHighLiftJets
import Proof.SmoothFiniteJetDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

lemma scalarHigherFamilyFromRotationData_two_jets
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ) (hCJ : 0 ≤ CJ)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (BQ BR : ℝ) (hQ : SmoothFiniteJetBound Q ((y,frameVectorLinear d.frame y),0) 2 BQ)
    (hR : ∀ ij,SmoothFiniteJetBound (R ij) ((y,frameVectorLinear d.frame y),0) 2 BR)
    (CG : ℝ) (hCG : 0 ≤ CG)
    (hAngular : ∀ i j,SmoothFiniteJetBound
      (normalFrameRelativeAngularDerivative d.γ A.scalarOperatorFamily i j)
      ((y,frameVectorLinear d.frame y),0) 2 (CG*(CJ*(d.radius y)^2))) :
    SmoothFiniteJetBound (A.scalarHigherFamilyFromRotationData Q R) ((y,frameVectorLinear d.frame y),0) 2
      (((19+9*Real.sqrt 2)*(4*CJ*((1+CG)*BQ+BR)))*(d.radius y)^2) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let B := 4*CJ*((1+CG)*BQ+BR)
  have hBR : 0 ≤ BR := (hR (0,0)).nonneg
  have hLowB : 4*CJ*BQ ≤ B := by
    dsimp only [B]
    nlinarith only [mul_nonneg hCJ (add_nonneg (mul_nonneg hCG hQ.nonneg) hBR)]
  have hDB : 4*CG*CJ*BQ+4*CJ*BR ≤ B := by
    dsimp only [B]
    nlinarith only [mul_nonneg hCJ hQ.nonneg]
  have hS3 := A.scalarOperatorFamily_three_jets hCJ
  have hS : SmoothFiniteJetBound A.scalarOperatorFamily p 2 (CJ*(d.radius y)^2) :=
    ⟨hS3.nonneg,hS3.smooth,fun n hn => hS3.bound n (by omega)⟩
  have hLow : SmoothFiniteJetBound (fun x => A.scalarOperatorFamily x (Q x)) p 2 (B*(d.radius y)^2) :=
    (hS.clm_apply_bound hQ).weaken (by
      calc
        _ = (4*CJ*BQ)*(d.radius y)^2 := by norm_num;ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hLowB (sq_nonneg _))
  have hD (ij : I × I) : SmoothFiniteJetBound (A.scalarRotationWitnessFromData Q R ij.1 ij.2) p 2
      (B*(d.radius y)^2) := by
    have hOne := (hAngular ij.1 ij.2).clm_apply_bound hQ
    have hTwo := hS.clm_apply_bound (hR ij)
    exact (hOne.add hTwo).weaken (by
      calc
        _ = (4*CG*CJ*BQ+4*CJ*BR)*(d.radius y)^2 := by norm_num;ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDB (sq_nonneg _))
  have hh := smoothFiniteJetBound_zero_order_rotation_high_lift _ _ p 2 (B*(d.radius y)^2) hLow hD
  exact hh.weaken (le_of_eq (by dsimp only [B];ring))
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
