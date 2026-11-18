import Proof.SphereOrderOneGraph
import Proof.Archive.SphereContinuousScalarMultiplier
import Proof.Archive.SharpRadialHarmonicCoefficientCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.SmoothSphereRotation OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SmoothAngularCasimir

def coarseSphereScalarMulL (q : C(UnitSphere,ℝ)) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((sphereContinuousScalarMulL q).comp
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem norm_coarseSphereScalarMulL_le (q : C(UnitSphere,ℝ)) : ‖coarseSphereScalarMulL q‖ ≤ ‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    (sphereContinuousScalarMulL q ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have h := (sphereContinuousScalarMulL q).le_opNorm
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm f)
  rw [LinearIsometryEquiv.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right (norm_sphereContinuousScalarMulL_le q) (norm_nonneg _))

def smoothDataProduct (f g : SmoothData) : SmoothData := ⟨fun x => f.1 x*g.1 x,f.2.mul g.2⟩

theorem coarseSphereScalarMulL_smooth (m f : SmoothData) :
    coarseSphereScalarMulL (smoothSphereValue m)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (smoothSphereLift f.1 f.2)) =
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (smoothSphereLift (smoothDataProduct m f).1 (smoothDataProduct m f).2) := by
  change sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    (sphereContinuousScalarMulL (smoothSphereValue m)
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (smoothSphereLift f.1 f.2)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics)
    (sphereContinuousScalarMulL_toLp (smoothSphereValue m) (smoothSphereValue f))

def smoothRotationData (i j : Fin 3) (f : SmoothData) : SmoothData :=
  ⟨sphereRotationDerivative i j f.1,contDiff_sphereRotationDerivative i j f.1 f.2⟩

theorem orderOneRotation_coefficient (u : SphereSobolev 1) (i j : Fin 3) (k : ℕ) :
    sphereSobolevCoefficientL 0 k (sphereSobolevRotationL 1 i j u) =
      harmonicSphereRotation k i j (sphereSobolevCoefficientL 1 k u) := by
  have hIndex (s t : ℝ) (h : s = t) :
      (sphereSobolevCoefficientL s k : SphereSobolev 0 →L[ℝ] harmonicSphereSubspace k) =
        sphereSobolevCoefficientL t k := by
    cases h
    rfl
  exact (congrArg (fun A : SphereSobolev 0 →L[ℝ] harmonicSphereSubspace k =>
    A (sphereSobolevRotationL 1 i j u)) (hIndex (1-1) 0 (by ring))).symm.trans
      (sphereSobolevCoefficientL_rotation 1 i j k u)

theorem smoothRotationData_product (i j : Fin 3) (m f : SmoothData) (x : X) :
    (smoothRotationData i j (smoothDataProduct m f)).1 x =
      (smoothRotationData i j m).1 x*f.1 x+m.1 x*(smoothRotationData i j f).1 x := by
  change fderiv ℝ (m.1*f.1) x (rotationVector i j x) = _
  rw [fderiv_mul (m.2.differentiable (by norm_num)).differentiableAt
    (f.2.differentiable (by norm_num)).differentiableAt]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  change m.1 x*fderiv ℝ f.1 x (rotationVector i j x)+f.1 x*fderiv ℝ m.1 x (rotationVector i j x) = _
  dsimp only [smoothRotationData,sphereRotationDerivative]
  ring

/-- For any H1 datum with a smooth L2 realization, the stored spectral
    rotation is exactly the rotation of that realization. -/
theorem orderOneRotation_smooth (u : SphereSobolev 1) (f : SmoothData)
    (hReal : sphereSobolevInclusionL 1 0 (by norm_num) u =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (smoothSphereLift f.1 f.2))
    (i j : Fin 3) :
    sphereSobolevRotationL 1 i j u =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (smoothSphereLift (smoothRotationData i j f).1 (smoothRotationData i j f).2) := by
  apply sphereSobolev_ext 0
  intro k
  have hIn := congrArg (sphereSobolevCoefficientL 0 k) hReal
  simp only [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv] at hIn
  have hRot := orderOneRotation_coefficient u i j k
  exact hRot.trans ((congrArg (harmonicSphereRotation k i j) hIn).trans
    ((sphereHarmonicCoordinate_sphereRotationDerivative orthogonalSphereHarmonics denseSphereHarmonics
      k i j f.1 f.2).symm.trans (sphereSobolevCoefficientL_zeroEquiv
        orthogonalSphereHarmonics denseSphereHarmonics k _).symm))

end ShrinkingSpheres
