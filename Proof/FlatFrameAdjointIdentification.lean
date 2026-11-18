import Proof.FlatNormalizedAngularOperators
import Proof.PhysicalFixedCenterGradient
import Proof.FirstAdjointNormalForm
import Proof.ConormalFirstAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem boundaryGradientL_constant_vector (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (F : I → SmoothCoefficientJets 2) (c : I → ℝ)
    (hF : ∀ j,∀ w : UnitSphere,coefficientValue 2 (F j) w.val = c j) :
    boundaryGradientL F sphereSobolevDegreeL =
      ∑ j : I,c j • boundaryGradientL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL := by
  let A := boundaryGradientL F sphereSobolevDegreeL
  let C := ∑ j : I,c j • boundaryGradientL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL
  have hHigh (f : SphereSobolev (3/2:ℝ)) :
      A (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
        C (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) := by
    let u := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f
    have hInput : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u =
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f :=
      congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f)
        (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
    have hValue := fixedHalfValueTrace_harmonicLift f
    have hNative := boundaryGradientL_nativeH2 F sphereSobolevDegreeL (fixedHarmonicLiftL f) u
      (hValue.trans hInput.symm) (sphereSobolevDegreeL_harmonicLift f)
    have hSphere (j : I) : smoothSphereValue (coefficientSmoothData (F j)) = ContinuousMap.const UnitSphere (c j) :=
      ContinuousMap.ext (hF j)
    rw [show A = boundaryGradientL F sphereSobolevDegreeL from rfl]
    rw [hNative]
    simp only [hSphere,sphereContinuousScalarMulL_const_apply,map_sum,map_smul]
    dsimp only [C]
    simp only [_root_.sum_apply,_root_.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z : SphereSobolev 0 => c j • z) (coordinateBoundaryGradientL_high Q hQ j f).symm
  exact DFunLike.ext' ((denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).equalizer
    A.continuous C.continuous (funext hHigh))

/-- Coframe combinations in the physical adjoint are the same combinations
    of the harmonic raising operators. This identity uses frame values only. -/
theorem boundaryGradientAdjointL_constant_vector (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (F : I → SmoothCoefficientJets 2) (c : I → ℝ)
    (hF : ∀ j,∀ w : UnitSphere,coefficientValue 2 (F j) w.val = c j) :
    boundaryGradientAdjointL F sphereSobolevDegreeL =
      ∑ j : I,c j • boundaryGradientAdjointL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL := by
  have hForward := boundaryGradientL_constant_vector Q hQ F c hF
  apply boundary_operator_eq_of_inner
  intro u v
  have h := boundaryGradientL_adjoint F sphereSobolevDegreeL sphereSobolevDegreeL
    sphereSobolevDegreeL_symmetric v u
  have hFv := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v) hForward
  rw [hFv] at h
  simp only [_root_.sum_apply,_root_.smul_apply,sum_inner,real_inner_smul_left] at h
  calc
    _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) v,boundaryGradientAdjointL F sphereSobolevDegreeL u⟫_ℝ := real_inner_comm _ _
    _ = ∑ j : I,c j*⟪boundaryGradientL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL v,
        sphereSobolevInclusionL 1 0 (by norm_num) u⟫_ℝ := h.symm
    _ = ∑ j : I,c j*⟪sphereSobolevInclusionL 1 0 (by norm_num) v,
        boundaryGradientAdjointL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL u⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun t : ℝ => c j*t) (boundaryGradientL_adjoint (coordinateBoundaryCoefficients Q j)
        sphereSobolevDegreeL sphereSobolevDegreeL sphereSobolevDegreeL_symmetric v u)
    _ = _ := by simp only [_root_.sum_apply,_root_.smul_apply,sum_inner,real_inner_smul_left];
                apply Finset.sum_congr rfl;intro j _;rw [real_inner_comm]

theorem fixedCenterCoefficient_sphere (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) (j : I) (w : UnitSphere) :
    coefficientValue 2 (fixedCenterCoefficient Q g e y a j) w.val = frameCoordinateLinear g e y j a := by
  have hw : w.val ∈ Metric.closedBall (0:X) 1 := by
    have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
    simpa [Metric.mem_closedBall,dist_zero_right,hn]
  exact (constantBoundaryCoefficient_germ Q hQ _ w.val hw).eq_of_nhds

theorem fixedCenterBoundaryAdjointL_eq_sum (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) :
    boundaryGradientAdjointL (fixedCenterCoefficient Q g e y a) sphereSobolevDegreeL =
      ∑ j : I,frameCoordinateLinear g e y j a •
        boundaryGradientAdjointL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL :=
  boundaryGradientAdjointL_constant_vector Q hQ _ _ (fixedCenterCoefficient_sphere Q hQ g e y a)

theorem fixedCenterCoefficient_frame (Q : SmoothCoefficientJets 2) (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (i : I) :
    fixedCenterCoefficient Q g e y (e y i) = coordinateBoundaryCoefficients Q i := by
  funext j
  simp only [fixedCenterCoefficient,coordinateBoundaryCoefficients,frameCoordinateLinear_apply,he,eq_comm]

theorem modelBoundaryAdjointL_eq_coframe_raising (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) (r b : ℝ) :
    modelBoundaryAdjointL (fixedCenterCoefficient Q g e y a) r b =
      r⁻¹ • (∑ j : I,frameCoordinateLinear g e y j a •
        boundaryGradientAdjointL (coordinateBoundaryCoefficients Q j) sphereSobolevDegreeL)+b • sphereSobolevDegreeL :=
  congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => r⁻¹ • T+b • sphereSobolevDegreeL)
    (fixedCenterBoundaryAdjointL_eq_sum Q hQ g e y a)

/-- The leading physical model is expressed using the very same bounded
    normalized raising operators as the already checked angular estimate. -/
theorem modelBoundaryAdjointL_normalized_apply (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) (r b : ℝ) (u : SphereSobolev 1) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (modelBoundaryAdjointL (fixedCenterCoefficient Q g e y a) r b u) =
        r⁻¹ • (∑ j : I,frameCoordinateLinear g e y j a •
          OAI.AnisotropicCalderon.BoundedAngularShift.normalizedRaising sphereFischerInner
            orthogonalSphereHarmonics denseSphereHarmonics j
              ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
                (sphereSobolevBesselEquiv 1 1 u)))+
          b • (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (sphereSobolevDegreeL u) := by
  have hModel := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
    (modelBoundaryAdjointL_eq_coframe_raising Q hQ g e y a r b)
  have h := congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm hModel
  simpa only [_root_.add_apply,_root_.smul_apply,_root_.sum_apply,map_add,map_smul,map_sum,
    coordinateBoundaryGradientAdjointL_normalized Q hQ] using h

end ShrinkingSpheres
