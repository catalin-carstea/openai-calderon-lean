import Proof.BoundaryGradientAdjoint
import Proof.BoundaryAngularCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarseSphereScalarMulL_zeroEquiv (q : C(UnitSphere,ℝ)) (u : SphereL2) :
    coarseSphereScalarMulL q (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics u) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (sphereContinuousScalarMulL q u) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  change Z (sphereContinuousScalarMulL q (Z.symm (Z u))) = _
  rw [Z.symm_apply_apply]

/-- The bounded H1 tangential action is the tangential part of the genuine
    coordinate trace of any H2 extension with that boundary value. -/
theorem coarseSphereTangentialL_nativeH2 (U : BallSobolev 2) (u : SphereSobolev 1)
    (hTrace : OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
        (TauCeti.Wkp.firstOrder 1 U) = sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
    (j : I) :
    coarseSphereTangentialL j u = sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j U-
        sphereCoordinateMulL j (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U)) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let t := strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j U-
    sphereCoordinateMulL j (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U)
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hNative := sphereTangentialDerivativeL_nativeHalfTrace_H2 fixedSobolevCalculus
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace U j
  have hJ := sphereSobolevInclusionL_eq_of_target_eq 0 (-1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by ring)
  have hRight := congrArg (fun I : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => I (Z t)) hJ
  have hEq : J (coarseSphereTangentialL j u) = J (Z t) :=
    (coarseSphereTangentialL_half_compatible j u).symm.trans
      ((congrArg (fixedSphereTangentialL j) hTrace).symm.trans (hNative.trans hRight))
  exact sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num) hEq

theorem vectorNormal_multiplier_decomposition (F : I → SmoothCoefficientJets 2) (r : SphereL2) :
    sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F))) r =
      ∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))
        (sphereCoordinateMulL j r) := by
  have hq : smoothSphereValue (coefficientSmoothData (vectorNormalJet F)) =
      ∑ j : I,smoothSphereValue (coefficientSmoothData (F j))*sphereCoordinate j := by
    ext w
    simp only [ContinuousMap.sum_apply,ContinuousMap.mul_apply]
    change coefficientValue 2 (vectorNormalJet F) w.val = ∑ j : I,coefficientValue 2 (F j) w.val*w.val j
    rw [coefficientValue_vectorNormalJet]
    change (∑ j : I,w.val j*coefficientValue 2 (F j) w.val) = _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hq,sphereContinuousScalarMulL_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [sphereCoordinateMulL_eq_scalarMulL]
  exact (sphereContinuousScalarMulL_mul_apply _ _ r).symm

theorem vector_gradient_L2_decomposition (F : I → SmoothCoefficientJets 2)
    (b : I → SphereL2) (r : SphereL2) :
    (∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F j))) (b j)) =
      sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F))) r+
      ∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))
        (b j-sphereCoordinateMulL j r) := by
  simp_rw [map_sub]
  rw [Finset.sum_sub_distrib,vectorNormal_multiplier_decomposition]
  abel

/-- The operator whose adjoint was constructed is the actual weighted coordinate
    gradient trace of the same H2 solution, whenever its radial trace is D u. -/
theorem boundaryGradientL_nativeH2 (F : I → SmoothCoefficientJets 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (U : BallSobolev 2) (u : SphereSobolev 1)
    (hTrace : OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
      sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
        (TauCeti.Wkp.firstOrder 1 U) = sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)
    (hRadial : D u = sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U)) :
    boundaryGradientL F D u = sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))
        (strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j U)) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let b (j : I) := strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j U
  let r := outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U
  have hT : coarseBoundaryTangentialL F u = Z
      (∑ j : I,sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))
        (b j-sphereCoordinateMulL j r)) := by
    rw [coarseBoundaryTangentialL_eq_sum]
    simp only [_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (congrArg (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j))))
      (coarseSphereTangentialL_nativeH2 U u hTrace j)).trans
        (coarseSphereScalarMulL_zeroEquiv _ _)
  have hN : coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F))) (D u) =
      Z (sphereContinuousScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F))) r) :=
    (congrArg (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (vectorNormalJet F)))) hRadial).trans
      (coarseSphereScalarMulL_zeroEquiv _ _)
  change coarseBoundaryTangentialL F u+_ = _
  have hSum := congrArg₂ (fun x y : SphereSobolev 0 => x+y) hT hN
  exact hSum.trans ((Z.map_add _ _).symm.trans (congrArg Z
    ((add_comm _ _).trans (vector_gradient_L2_decomposition F b r).symm)))

end ShrinkingSpheres
