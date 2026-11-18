import Proof.ClosedGradientAngularExpansion
import Proof.ContinuousOperatorCurveCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open scoped BigOperators
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def coordinateGradientAdjointOperator (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (k : I) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (CoarseAngularFields.coordinateTangentialAdjoint k).operator+Da.comp (oneSphereCoordinateMulL k)

lemma coordinateGradientAdjoint_operator (P : CoarseAngularFields) (k : I) :
    (CoarseAngularFields.coordinateGradientAdjoint P k).operator =
      coordinateGradientAdjointOperator P.operator k := rfl

lemma closedGradient_coordinate_sum (Q : I → ClosedCoefficientJets 3)
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    closedBoundaryGradientAdjoint Q Da = ∑ k : I,(coordinateGradientAdjointOperator Da k).comp
      (closedOneBoundaryScalarMultiplierL (Q k)) := by
  let P : CoarseAngularFields := ⟨Da,0,0,0⟩
  exact (CoarseAngularFields.gradient_operator Q P).symm.trans
    (CoarseAngularFields.gradient_coordinate_sum Q P)

lemma hasDerivAt_closedGradient_curve (Q : ℝ → I → ClosedCoefficientJets 3)
    (Da : ℝ → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (dQ : I → SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (dDa : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (t : ℝ)
    (hQ : ∀ k,HasDerivAt (fun θ => closedOneBoundaryScalarMultiplierL (Q θ k)) (dQ k) t)
    (hDa : HasDerivAt Da dDa t) :
    HasDerivAt (fun θ => closedBoundaryGradientAdjoint (Q θ) (Da θ))
      ((∑ k : I,(coordinateGradientAdjointOperator (Da t) k).comp (dQ k))+
        dDa.comp (closedVectorNormalMultiplier (Q t))) t := by
  have hB (k : I) : HasDerivAt (fun θ => coordinateGradientAdjointOperator (Da θ) k)
      (dDa.comp (oneSphereCoordinateMulL k)) t := by
    exact hasDerivAt_const_add_comp_const Da dDa t hDa
      (CoarseAngularFields.coordinateTangentialAdjoint k).operator (oneSphereCoordinateMulL k)
  have hh := hasDerivAt_sum_clm_comp
    (fun k θ => coordinateGradientAdjointOperator (Da θ) k)
    (fun k => dDa.comp (oneSphereCoordinateMulL k))
    (fun k θ => closedOneBoundaryScalarMultiplierL (Q θ k)) dQ t hB hQ
  have hFun : (fun θ => ∑ k : I,(coordinateGradientAdjointOperator (Da θ) k).comp
      (closedOneBoundaryScalarMultiplierL (Q θ k))) =
      (fun θ => closedBoundaryGradientAdjoint (Q θ) (Da θ)) := by
    funext θ
    exact (closedGradient_coordinate_sum _ _).symm
  rw [hFun] at hh
  have hVal : (∑ k : I,((dDa.comp (oneSphereCoordinateMulL k)).comp
      (closedOneBoundaryScalarMultiplierL (Q t k))+
      (coordinateGradientAdjointOperator (Da t) k).comp (dQ k))) =
      (∑ k : I,(coordinateGradientAdjointOperator (Da t) k).comp (dQ k))+
        dDa.comp (closedVectorNormalMultiplier (Q t)) := by
    rw [Finset.sum_add_distrib]
    have hSum : (∑ k : I,(dDa.comp (oneSphereCoordinateMulL k)).comp
        (closedOneBoundaryScalarMultiplierL (Q t k))) = dDa.comp (closedVectorNormalMultiplier (Q t)) := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [closedVectorNormalMultiplier,_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
    rw [hSum,add_comm]
  exact hh.congr_deriv hVal
end ShrinkingSpheres
