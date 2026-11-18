import Proof.NormalCoefficientAngularData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def linearScalarAngularNormBudget (Q : SmoothCoefficientJets 2) : ℝ :=
  ‖linearScalarClosedCoefficientL Q‖+
    ∑ ij : I × I,‖(linearScalarClosedCoefficientL Q).comp (rotationCovectorMapL ij.1 ij.2)‖

lemma linearScalarAngularNormBudget_nonneg (Q : SmoothCoefficientJets 2) :
    0 ≤ linearScalarAngularNormBudget Q := by unfold linearScalarAngularNormBudget;positivity

lemma linearScalar_augmented_norm_le (Q : SmoothCoefficientJets 2) (ell : X →L[ℝ] ℝ) :
    ‖linearScalarClosedCoefficientL Q ell‖+
      ∑ ij : I × I,‖linearScalarClosedCoefficientL Q (rotationCovector ell ij.1 ij.2)‖ ≤
      linearScalarAngularNormBudget Q*‖ell‖ := by
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun (ij : I × I) _ =>
    ((linearScalarClosedCoefficientL Q).comp (rotationCovectorMapL ij.1 ij.2)).le_opNorm ell)
  simp only [ContinuousLinearMap.comp_apply,rotationCovectorMapL_apply] at hSum
  exact (add_le_add ((linearScalarClosedCoefficientL Q).le_opNorm ell) hSum).trans_eq
    (by rw [linearScalarAngularNormBudget,add_mul,Finset.sum_mul])

namespace RelativeNormalScalarRemainderFamily
variable {d : Data} {y : X} {CR : ℝ}

lemma remainder_augmented_norm_le (R : RelativeNormalScalarRemainderFamily d y CR)
    (CG : ℝ)
    (hAngular : ∀ ij : I × I,‖normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CG*(CR*(d.radius y)^2)) :
    ‖R.closed ((y,frameVectorLinear d.frame y),0)‖+
      ∑ ij : I × I,‖normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2
        ((y,frameVectorLinear d.frame y),0)‖ ≤ (1+9*CG)*CR*(d.radius y)^2 := by
  have hR : ‖R.closed ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*(d.radius y)^2 := by
    simpa only [RelativeNormalScalarRemainderFamily.closed,norm_iteratedFDeriv_zero] using R.jets.bound 0 (by norm_num)
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun ij _ => hAngular ij)
  have hNine : (∑ _ : I × I,CG*(CR*(d.radius y)^2))=9*(CG*(CR*(d.radius y)^2)) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  rw [hNine] at hSum
  exact (add_le_add hR hSum).trans_eq (by ring)

lemma normalCoefficient_augmented_norm_le (R : RelativeNormalScalarRemainderFamily d y CR)
    (Q : SmoothCoefficientJets 2) (CQ CG : ℝ) (hCQ : 0 ≤ CQ) (hCR : 0 ≤ CR) (hCG : 0 ≤ CG)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : ‖normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0)‖ ≤ CQ)
    (hAngular : ∀ ij : I × I,‖normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CG*(CR*(d.radius y)^2)) :
    ‖R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0)‖+
      ∑ ij : I × I,‖R.normalAngularCoefficient Q ij.1 ij.2 ((y,frameVectorLinear d.frame y),0)‖ ≤
      ‖closedUnitCoefficient Q‖+linearScalarAngularNormBudget Q*CQ+(1+9*CG)*CR := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁ p
  have hN : ‖R.normalCoefficient Q p‖ ≤
      ‖closedUnitCoefficient Q‖+d.radius y*‖linearScalarClosedCoefficientL Q ell‖+‖R.closed p‖ := by
    have hh := (norm_add_le (closedUnitCoefficient Q+d.radius y • linearScalarClosedCoefficientL Q ell) (R.closed p)).trans
      (add_le_add (norm_add_le (closedUnitCoefficient Q) (d.radius y • linearScalarClosedCoefficientL Q ell)) le_rfl)
    simpa only [normalCoefficient,closedUnitCoefficient,ell,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] using hh
  have hS := Finset.sum_le_sum (s:=Finset.univ) (fun (ij : I × I) _ =>
    norm_add_le (d.radius y • linearScalarClosedCoefficientL Q (rotationCovector ell ij.1 ij.2))
      (normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2 p))
  simp only [normalAngularCoefficient,ell,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
    Finset.sum_add_distrib,← Finset.mul_sum] at hS
  have hAug := (linearScalar_augmented_norm_le Q ell).trans
    (mul_le_mul_of_nonneg_left hEll (linearScalarAngularNormBudget_nonneg Q))
  have hR := R.remainder_augmented_norm_le CG hAngular
  have hR2 : (d.radius y)^2 ≤ 1 := by nlinarith
  have hLPos : 0 ≤ linearScalarAngularNormBudget Q*CQ := mul_nonneg (linearScalarAngularNormBudget_nonneg Q) hCQ
  have hRPos : 0 ≤ (1+9*CG)*CR := by positivity
  calc
    _ ≤ ‖closedUnitCoefficient Q‖+
        d.radius y*(‖linearScalarClosedCoefficientL Q ell‖+
          ∑ ij : I × I,‖linearScalarClosedCoefficientL Q (rotationCovector ell ij.1 ij.2)‖)+
        (‖R.closed p‖+∑ ij : I × I,‖normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2 p‖) :=
      (add_le_add hN hS).trans_eq (by ring)
    _ ≤ ‖closedUnitCoefficient Q‖+d.radius y*(linearScalarAngularNormBudget Q*CQ)+
        (1+9*CG)*CR*(d.radius y)^2 :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hAug hr)) hR
    _ ≤ _ := add_le_add
      (add_le_add le_rfl (mul_le_of_le_one_left hLPos hr1))
      (mul_le_of_le_one_right hRPos hR2)

lemma normalCoefficient_higher_deviation_norm_le (R : RelativeNormalScalarRemainderFamily d y CR)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (CQ : ℝ) (hCR : 0 ≤ CR) (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : ‖normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0)‖ ≤ CQ) :
    ‖closedThreeJetHigherScalarMultiplierL (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))-
      ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ))‖ ≤
      (‖closedThreeJetHigherScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR))*d.radius y := by
  have hDelta := R.norm_normalCoefficient_sub_unit_le Q CQ hCR hr hr1 hEll
  have hUnit := closedUnitCoefficient_higher Q hQ
  have hEq : closedThreeJetHigherScalarMultiplierL
      (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0)-closedUnitCoefficient Q)=
      closedThreeJetHigherScalarMultiplierL (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))-
        ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ)) :=
    (closedThreeJetHigherScalarMultiplierL.map_sub _ _).trans (congrArg
      (fun V : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) =>
        closedThreeJetHigherScalarMultiplierL (R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0))-V) hUnit)
  rw [← hEq]
  exact ((closedThreeJetHigherScalarMultiplierL).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hDelta (norm_nonneg _)).trans_eq (by ring))
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
