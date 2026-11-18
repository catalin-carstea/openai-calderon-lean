import Proof.RelativeAngularCoefficientCovariance
import Proof.BoundaryNormalContractionAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation OAI.AnisotropicCalderon.MetricOperator

lemma matrixNormalContraction_eq_dotProduct (A : Mat) (z : X) :
    matrixNormalContraction A z=(fun i => z i) ⬝ᵥ (A *ᵥ (fun i => z i)) := by
  simp only [matrixNormalContraction,dotProduct,Matrix.mulVec,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma matrixNormalContraction_coordinate_conjugation (A : Mat) (z : X) (i j : I) (θ : ℝ) :
    matrixNormalContraction ((coordinateRotationMatrix i j θ).transpose*A*coordinateRotationMatrix i j θ) z=
      matrixNormalContraction A (coordinateRotationIsometry i j θ z) := by
  have hVec : coordinateRotationMatrix i j θ *ᵥ (fun k => z k)=fun k => coordinateRotationIsometry i j θ z k := by
    ext k
    exact congrArg (fun u : X => u k)
      (operatorMatrixMap_apply (coordinateRotationIsometry i j θ).toContinuousLinearEquiv.toContinuousLinearMap z)
  rw [matrixNormalContraction_eq_dotProduct,matrixNormalContraction_eq_dotProduct,
    ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,hVec]

lemma Elliptic.normalScalarRemainder_angular_curve {Ω : Set X} {K : ℝ} {d : Data}
    (h : Elliptic Ω K d.γ) (hK : 0 < K) (r : ℝ)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω)
    (i j : I) (θ : ℝ) (w : UnitSphere) :
    normalFrameRelativeNormalScalarRemainder d r (normalFrameRelativeAngularCurve d.γ p i j θ,w.val)=
      normalFrameRelativeNormalScalarRemainder d r (p,coordinateRotationIsometry i j θ w.val) := by
  let wr : UnitSphere := ⟨coordinateRotationIsometry i j θ w.val,by
    simpa only [Metric.mem_sphere,dist_zero_right,(coordinateRotationIsometry i j θ).norm_map] using w.property⟩
  have hCoeff := h.normalFrameRelativeCoefficient_angular_curve hK d.g₁ d.expMap r p hp i j θ w.val
  have hEll := h.normalFrameRelativeFirstCovector_angular_curve hK d.g₁ p hp i j θ
  change matrixNormalContraction (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r
      (normalFrameRelativeAngularCurve d.γ p i j θ,w.val)-(1:Mat)-
      r • normalFrameRelativeFirstModel d.γ d.g₁ (normalFrameRelativeAngularCurve d.γ p i j θ,w.val)) w.val=_
  rw [matrixNormalContraction_sub,matrixNormalContraction_sub,matrixNormalContraction_one w,
    normalFrameRelativeFirstModel_scalar,matrixNormalContraction_smul,matrixNormalContraction_smul,
    matrixNormalContraction_one w,mul_one,hEll]
  change matrixNormalContraction (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r
      (normalFrameRelativeAngularCurve d.γ p i j θ,w.val)) w.val-1-
      r*(normalFrameRelativeFirstCovector d.γ d.g₁ p (coordinateRotationIsometry i j θ w.val))=_
  rw [hCoeff]
  change matrixNormalContraction ((coordinateRotationMatrix i j θ).transpose*
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r (p,wr.val)*coordinateRotationMatrix i j θ) w.val-1-_=_
  rw [matrixNormalContraction_coordinate_conjugation]
  change _=matrixNormalContraction (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r (p,wr.val)-(1:Mat)-
    r • normalFrameRelativeFirstModel d.γ d.g₁ (p,wr.val)) wr.val
  rw [matrixNormalContraction_sub,matrixNormalContraction_sub,matrixNormalContraction_one wr,
    normalFrameRelativeFirstModel_scalar,matrixNormalContraction_smul,matrixNormalContraction_smul,
    matrixNormalContraction_one wr,mul_one]
end ShrinkingSpheres
