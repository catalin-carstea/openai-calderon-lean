import Proof.FlatFrameAdjointIdentification
import Proof.MovingFrameSecond
import Proof.OrderOneCoefficientAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

theorem coarseSphereScalarMulL_sum_three (q : I → C(UnitSphere,ℝ)) :
    coarseSphereScalarMulL (∑ a : I,q a) = ∑ a : I,coarseSphereScalarMulL (q a) := by
  simp only [Fin.sum_univ_three,coarseSphereScalarMulL_add]

def fixedCenterNormalValue (Q : SmoothCoefficientJets 2) (g : MetricField) (e : Frame)
    (y a : X) : C(UnitSphere,ℝ) :=
  smoothSphereValue (coefficientSmoothData (vectorNormalJet (fixedCenterCoefficient Q g e y a)))

theorem fixedCenterNormalValue_apply (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) (w : UnitSphere) :
    fixedCenterNormalValue Q g e y a w = ∑ j : I,w.val j*frameCoordinateLinear g e y j a := by
  change coefficientValue 2 (vectorNormalJet (fixedCenterCoefficient Q g e y a)) w.val = _
  rw [coefficientValue_vectorNormalJet]
  change (∑ j : I,w.val j*coefficientValue 2 (fixedCenterCoefficient Q g e y a j) w.val) = _
  simp_rw [fixedCenterCoefficient_sphere Q hQ]

theorem fixedCenterNormalValue_axis_expansion (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) :
    fixedCenterNormalValue Q g e y a = ∑ k : I,a k • fixedCenterNormalValue Q g e y (axis k) := by
  ext w
  simp only [ContinuousMap.coe_sum,Finset.sum_apply,ContinuousMap.coe_smul,Pi.smul_apply,smul_eq_mul]
  simp_rw [fixedCenterNormalValue_apply Q hQ]
  simp_rw [linear_axis_expansion (frameCoordinateLinear g e y _) a]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fixedCenterNormalMulL_axis_expansion (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) :
    coarseSphereScalarMulL (fixedCenterNormalValue Q g e y a) =
      ∑ k : I,a k • coarseSphereScalarMulL (fixedCenterNormalValue Q g e y (axis k)) := by
  have hValue := congrArg coarseSphereScalarMulL (fixedCenterNormalValue_axis_expansion Q hQ g e y a)
  have hSum := coarseSphereScalarMulL_sum_three (fun k => a k • fixedCenterNormalValue Q g e y (axis k))
  have hFinal := hValue.trans hSum
  simpa only [coarseSphereScalarMulL_smul] using hFinal

theorem firstBoundaryAdjointCorrectionL_axis_expansion (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0)
    (r : ℝ) (ell : X →L[ℝ] ℝ) :
    firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q g e y a) B r (ell a) =
      ∑ k : I,a k • firstBoundaryAdjointCorrectionL (fixedCenterCoefficient Q g e y (axis k)) B r (ell (axis k)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [_root_.sum_apply,_root_.smul_apply]
  have hNormal := congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => B.adjoint (T u))
    (fixedCenterNormalMulL_axis_expansion Q hQ g e y a)
  simp only [_root_.sum_apply,_root_.smul_apply,map_sum,map_smul] at hNormal
  change B.adjoint (coarseSphereScalarMulL (fixedCenterNormalValue Q g e y a) u)+
      (r*ell a) • B.adjoint u = _
  have hEll : (r*ell a) • B.adjoint u =
      ∑ k : I,a k • ((r*ell (axis k)) • B.adjoint u) := by
    have hScalar := congrArg (fun t : ℝ => (r*t) • B.adjoint u) (linear_axis_expansion ell a)
    apply hScalar.trans
    simp only [Finset.mul_sum,Finset.sum_smul,smul_smul]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    ring
  have hSum := congrArg₂ (fun x y : SphereSobolev 0 => x+y) hNormal hEll
  apply hSum.trans
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [firstBoundaryAdjointCorrectionL,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,smul_add,fixedCenterNormalValue]

theorem modelBoundaryAdjointL_axis_expansion (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) (r : ℝ) (ell : X →L[ℝ] ℝ) :
    modelBoundaryAdjointL (fixedCenterCoefficient Q g e y a) r (ell a) =
      ∑ k : I,a k • modelBoundaryAdjointL (fixedCenterCoefficient Q g e y (axis k)) r (ell (axis k)) := by
  let R (j : I) := boundaryGradientAdjointL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL
  let T : X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (∑ j : I,(frameCoordinateLinear g e y j).smulRight (r⁻¹ • R j))+
      ell.smulRight sphereSobolevDegreeL
  have hT (v : X) : T v = modelBoundaryAdjointL (fixedCenterCoefficient Q g e y v) r (ell v) := by
    have hScale : (∑ j : I,frameCoordinateLinear g e y j v • (r⁻¹ • R j)) =
        r⁻¹ • (∑ j : I,frameCoordinateLinear g e y j v • R j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact smul_comm _ _ _
    calc
      _ = (∑ j : I,frameCoordinateLinear g e y j v • (r⁻¹ • R j))+ell v • sphereSobolevDegreeL := by
        simp only [T,_root_.add_apply,_root_.sum_apply,ContinuousLinearMap.smulRight_apply]
      _ = r⁻¹ • (∑ j : I,frameCoordinateLinear g e y j v • R j)+ell v • sphereSobolevDegreeL :=
        congrArg (fun S : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => S+ell v • sphereSobolevDegreeL) hScale
      _ = _ := (modelBoundaryAdjointL_eq_coframe_raising Q hQ g e y v r (ell v)).symm
  have h := congrArg T (axis_expansion a)
  rw [map_sum] at h
  simp only [map_smul] at h
  simpa only [hT] using h.symm

end ShrinkingSpheres
