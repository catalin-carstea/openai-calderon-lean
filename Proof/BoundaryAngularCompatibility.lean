import Proof.BoundaryAngularAdjoint
import Proof.ActualLowRadialEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection

theorem coarseSphereCoordinateMulL_eq_sobolev (i : I) :
    coarseSphereScalarMulL (sphereCoordinate i) =
      sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics 0
        (EuclideanSpace.single i 1) := by
  apply ContinuousLinearMap.ext
  intro u
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have h := sphereSobolevLinearCoordinateMulL_zeroEquiv sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (EuclideanSpace.single i 1) (Z.symm u)
  have hA := (sphereLinearCoordinateMulL_single i).trans (sphereCoordinateMulL_eq_scalarMulL i)
  have hInput := congrArg
    (sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics 0 (EuclideanSpace.single i 1))
    (Z.apply_symm_apply u)
  exact ((congrArg (fun A : SphereL2 →L[ℝ] SphereL2 => Z (A (Z.symm u))) hA).symm.trans h.symm).trans hInput

theorem rotation_one_half_compatible (u : SphereSobolev 1) (i j : I) :
    sphereSobolevInclusionL 0 (-1/2:ℝ) (by norm_num) (sphereSobolevRotationL 1 i j u) =
      sphereSobolevRotationL (1/2:ℝ) i j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
  apply sphereSobolev_ext (-1/2:ℝ)
  intro k
  have hL := (sphereSobolevCoefficientL_inclusion 0 (-1/2:ℝ) (by norm_num) (sphereSobolevRotationL 1 i j u) k).trans
    (orderOneRotation_coefficient u i j k)
  have hIndex := congrArg (fun s : ℝ => sphereSobolevCoefficientL s k
    (sphereSobolevRotationL (1/2:ℝ) i j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)))
      (show (1/2:ℝ)-1 = -1/2 by ring)
  have hR := hIndex.symm.trans
    ((sphereSobolevCoefficientL_rotation (1/2:ℝ) i j k _).trans
      (congrArg (harmonicSphereRotation k i j) (sphereSobolevCoefficientL_inclusion 1 (1/2:ℝ) (by norm_num) u k)))
  exact hL.trans hR.symm

def coarseSphereTangentialL (j : I) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ i : I,(coarseSphereScalarMulL (sphereCoordinate i)).comp (sphereSobolevRotationL 1 i j)

theorem coarseSphereTangentialL_half_compatible (j : I) (u : SphereSobolev 1) :
    fixedSphereTangentialL j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (coarseSphereTangentialL j u) := by
  let J := sphereSobolevInclusionL 0 (-1/2:ℝ) (by norm_num)
  have hTerm (i : I) :
      sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics (-1/2:ℝ)
        (EuclideanSpace.single i 1)
        (sphereSobolevRotationL (1/2:ℝ) i j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) =
      J (coarseSphereScalarMulL (sphereCoordinate i) (sphereSobolevRotationL 1 i j u)) := by
    have hRotation := rotation_one_half_compatible u i j
    have hCoord := sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics 0 (-1/2:ℝ) (by norm_num) (EuclideanSpace.single i 1) (sphereSobolevRotationL 1 i j u)
    have hScalar := congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
      J (A (sphereSobolevRotationL 1 i j u))) (coarseSphereCoordinateMulL_eq_sobolev i)
    exact (congrArg
      (sphereSobolevLinearCoordinateMulL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics (-1/2:ℝ)
        (EuclideanSpace.single i 1)) hRotation.symm).trans (hCoord.symm.trans hScalar.symm)
  have hSum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _ => hTerm i)
  have hPoint : fixedSphereTangentialL j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) =
      J (coarseSphereTangentialL j u) := by
    simpa only [fixedSphereTangentialL,sphereTangentialDerivativeL,coarseSphereTangentialL,
      _root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum] using hSum
  have hJ := sphereSobolevInclusionL_eq_of_target_eq 0 (-1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (by norm_num) (by ring)
  exact hPoint.trans (congrArg (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A (coarseSphereTangentialL j u)) hJ)

theorem coarseBoundaryTangentialL_eq_sum (F : I → SmoothCoefficientJets 2) :
    coarseBoundaryTangentialL F = ∑ j : I,
      (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))).comp
        (coarseSphereTangentialL j) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [coarseBoundaryTangentialL,coarseSphereTangentialL,_root_.sum_apply,ContinuousLinearMap.comp_apply,map_sum]

theorem boundaryTangential_endpoints_compatible (F : I → SmoothCoefficientJets 2) :
    (∑ j : I,(negativeBoundaryCoefficientMulL (F j)).comp (fixedSphereTangentialL j)).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) =
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (coarseBoundaryTangentialL F) := by
  apply ContinuousLinearMap.ext
  intro u
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  have hTerm (j : I) :
      negativeBoundaryCoefficientMulL (F j) (fixedSphereTangentialL j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u)) =
      J (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (F j)))
        (coarseSphereTangentialL j u)) :=
    (congrArg (negativeBoundaryCoefficientMulL (F j)) (coarseSphereTangentialL_half_compatible j u)).trans
      (negativeBoundaryCoefficientMulL_coarse (F j) (coarseSphereTangentialL j u))
  have hSum := (Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ => hTerm j)).trans (map_sum J _ _).symm
  have hEq := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => J (A u)) (coarseBoundaryTangentialL_eq_sum F)
  exact hSum.trans hEq.symm

end ShrinkingSpheres
