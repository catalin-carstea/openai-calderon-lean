import Proof.BoundarySmoothMultiplier
import Proof.FiberFischer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SpectralCoreRegularity OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open OAI.AnisotropicCalderon.SmoothSphereRotation OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SmoothAngularCasimir
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.GreenRadialTrace

theorem coarseSphereScalarMulL_rotation_product (m f : SmoothData) (i j : Fin 3) :
    coarseSphereScalarMulL (smoothSphereValue (smoothRotationData i j m))
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (smoothSphereLift f.1 f.2))+
    coarseSphereScalarMulL (smoothSphereValue m)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (smoothSphereLift (smoothRotationData i j f).1 (smoothRotationData i j f).2)) =
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (smoothSphereLift (smoothRotationData i j (smoothDataProduct m f)).1
        (smoothRotationData i j (smoothDataProduct m f)).2) := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let a := smoothDataProduct (smoothRotationData i j m) f
  let b := smoothDataProduct m (smoothRotationData i j f)
  have hSum := congrArg₂ (fun x y : SphereSobolev 0 => x+y)
    (coarseSphereScalarMulL_smooth (smoothRotationData i j m) f)
    (coarseSphereScalarMulL_smooth m (smoothRotationData i j f))
  have hLift : smoothSphereLift a.1 a.2+smoothSphereLift b.1 b.2 =
      smoothSphereLift (smoothRotationData i j (smoothDataProduct m f)).1
        (smoothRotationData i j (smoothDataProduct m f)).2 := by
    have hAdd := (smoothSphereLift_add a.1 b.1 a.2 b.2).symm
    refine hAdd.trans ?_
    have hFun : (fun x => a.1 x+b.1 x) = (smoothRotationData i j (smoothDataProduct m f)).1 := by
      funext x
      exact (smoothRotationData_product i j m f x).symm
    change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
      (ContinuousMap.toLp 2 sphereProbability ℝ) _
    congr 1
    ext w
    exact congrFun hFun w.val
  exact hSum.trans ((Z.map_add _ _).symm.trans (congrArg Z hLift))

/-- Every H1 realization of multiplication by a smooth scalar satisfies the
    exact L2 rotation product rule. This uses dense finite harmonic inputs. -/
theorem orderOneMultiplier_rotation_product (m : SmoothData)
    (T : SphereSobolev 1 →L[ℝ] SphereSobolev 1)
    (hT : ∀ u,sphereSobolevInclusionL 1 0 (by norm_num) (T u) =
      coarseSphereScalarMulL (smoothSphereValue m) (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (i j : Fin 3) :
    (sphereSobolevRotationL 1 i j).comp T =
      (coarseSphereScalarMulL (smoothSphereValue (smoothRotationData i j m))).comp
        (sphereSobolevInclusionL 1 0 (by norm_num))+
      (coarseSphereScalarMulL (smoothSphereValue m)).comp (sphereSobolevRotationL 1 i j) := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  let p := harmonicPolynomialRepresentativeL sphereFischerInner k a
  let f : SmoothData := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  let u := sphereSobolevSingleL 1 k a
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hPoly : smoothSphereLift f.1 f.2 = (a : SphereL2) :=
    (smoothSphereLift_polynomialEvaluation p).trans
      (polynomialSphereL2_harmonicPolynomialRepresentative sphereFischerInner k a)
  have hReal : sphereSobolevInclusionL 1 0 (by norm_num) u = Z (smoothSphereLift f.1 f.2) := by
    have hZ := sphereSobolevZeroEquiv_harmonic_subtype orthogonalSphereHarmonics denseSphereHarmonics k a
    exact (sphereSobolevInclusionL_single 1 0 (by norm_num) k a).trans (hZ.symm.trans (congrArg Z hPoly).symm)
  have hTReal : sphereSobolevInclusionL 1 0 (by norm_num) (T u) =
      Z (smoothSphereLift (smoothDataProduct m f).1 (smoothDataProduct m f).2) :=
    (hT u).trans ((congrArg (coarseSphereScalarMulL (smoothSphereValue m)) hReal).trans
      (coarseSphereScalarMulL_smooth m f))
  have hLeft := orderOneRotation_smooth (T u) (smoothDataProduct m f) hTReal i j
  have hRot := orderOneRotation_smooth u f hReal i j
  have hRight := congrArg₂ (fun x y : SphereSobolev 0 => x+y)
    (congrArg (coarseSphereScalarMulL (smoothSphereValue (smoothRotationData i j m))) hReal)
    (congrArg (coarseSphereScalarMulL (smoothSphereValue m)) hRot)
  exact hLeft.trans (hRight.trans (coarseSphereScalarMulL_rotation_product m f i j)).symm

end ShrinkingSpheres
