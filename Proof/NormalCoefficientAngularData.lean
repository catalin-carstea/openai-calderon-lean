import Proof.RelativeNormalScalarAngularCoefficient
import Proof.LinearScalarAngularCoefficient
import Proof.ClosedCoefficientAngularProduct
import Proof.CompletedNormalCoefficientFamily
import Proof.FirstRadialAngularFieldJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
namespace RelativeNormalScalarRemainderFamily
variable {d : Data} {y : X} {CR : ℝ}

def normalAngularCoefficient (R : RelativeNormalScalarRemainderFamily d y CR)
    (Q : SmoothCoefficientJets 2) (i j : I) (p : NormalFrameRelativeParameter) : ClosedCoefficientJets 3 :=
  d.radius y • linearScalarClosedCoefficientL Q
    (rotationCovector (normalFrameRelativeFirstCovector d.γ d.g₁ p) i j)+
    normalFrameRelativeAngularDerivative d.γ R.closed i j p

lemma normalAngularCoefficient_half (R : RelativeNormalScalarRemainderFamily d y CR)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {Ω : Set X} {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ R.domain)
    (hpPos : p ∈ normalFrameRelativePositiveDomain Ω)
    (he : ∀ i j,metricPair d.γ p.1.1 (p.1.2 (axis i)) (p.1.2 (axis j))=if i=j then 1 else 0)
    (i j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (R.normalAngularCoefficient Q i j p)=
      closedCoefficientAngularHalfL i j (R.normalCoefficient Q p) := by
  have hUnit : closedCoefficientAngularHalfL i j
      (smoothCoefficientClosureInclusionL 3 (coefficientThirdJet Q))=0 := closedUnitCoefficient_angular_half Q hQ i j
  simp only [normalAngularCoefficient,normalCoefficient,ContinuousLinearMap.map_add,
    ContinuousLinearMap.map_smul,linearScalarClosedCoefficient_angular_half Q hQ,
    R.angular_half h hK p hp hpPos he i j,hUnit,zero_add]

lemma norm_normalCoefficient_sub_unit_le (R : RelativeNormalScalarRemainderFamily d y CR)
    (Q : SmoothCoefficientJets 2) (CQ : ℝ) (hCR : 0 ≤ CR)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hEll : ‖normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0)‖ ≤ CQ) :
    ‖R.normalCoefficient Q ((y,frameVectorLinear d.frame y),0)-closedUnitCoefficient Q‖ ≤
      (‖linearScalarClosedCoefficientL Q‖*CQ+CR)*d.radius y := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hR : ‖R.closed p‖ ≤ CR*(d.radius y)^2 := by
    simpa only [RelativeNormalScalarRemainderFamily.closed,p,norm_iteratedFDeriv_zero] using R.jets.bound 0 (by norm_num)
  have hL := ((linearScalarClosedCoefficientL Q).le_opNorm
    (normalFrameRelativeFirstCovector d.γ d.g₁ p)).trans
      (mul_le_mul_of_nonneg_left hEll (norm_nonneg _))
  have hEq : R.normalCoefficient Q p-closedUnitCoefficient Q=
      d.radius y • linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)+R.closed p := by
    unfold normalCoefficient closedUnitCoefficient
    abel
  rw [hEq]
  have hNorm := norm_add_le
    (d.radius y • linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) (R.closed p)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hNorm
  have hR2 : (d.radius y)^2 ≤ d.radius y := by nlinarith
  exact (hNorm.trans (add_le_add (mul_le_mul_of_nonneg_left hL hr) hR)).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left hR2 hCR])
end RelativeNormalScalarRemainderFamily
end ShrinkingSpheres
