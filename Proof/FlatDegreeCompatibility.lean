import Proof.FirstRadialOrderZero
import Proof.ConormalSymmetry
import Proof.CoarseConormalSymmetry
import Proof.Archive.SphereSobolevShiftedPhysicalDegree

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory MvPolynomial
open scoped ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralWeightedGraph
open OAI.AnisotropicCalderon.AngularPolynomial OAI.AnisotropicCalderon.RotationCasimir
open OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion

theorem smoothRadialSphere_homogeneous (k : ℕ) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) :
    smoothRadialSphere (smoothPolynomialData p) = (k:ℝ) • polynomialSphere p := by
  ext w
  change fderiv ℝ (fun x : X => eval (polynomialCoordinateMap x) p) w.val w.val =
    (k:ℝ)*eval (polynomialCoordinateMap w.val) p
  have h := OAI.AnisotropicCalderon.HarmonicPolynomialGreen.inner_polynomial_energyGradient_radial k p hp w.val
  rw [energyGradient_eq_gradient,inner_gradient_right] at h
  simpa only [smoothPolynomialData,RCLike.conj_to_real] using h

theorem outwardRadialTrace_homogeneous (k : ℕ) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous k) :
    outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (polynomialBallSobolev 2 p) =
      (k:ℝ) • polynomialSphereL2 p := by
  have h := congrArg (ContinuousMap.toLp 2 sphereProbability ℝ) (smoothRadialSphere_homogeneous k p hp)
  exact (outwardRadialTraceL_polynomialBallSobolev fixedSobolevCalculus fixedUnitBallValueTrace p).trans
    (h.trans ((ContinuousMap.toLp 2 sphereProbability ℝ).map_smul (k:ℝ) (polynomialSphere p)))

theorem fixedLowRadialL_single (k : ℕ) (a : harmonicSphereSubspace k) :
    fixedLowRadialL (sphereSobolevSingleL (1/2:ℝ) k a) =
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) ((k:ℝ) • sphereSobolevSingleL 0 k a) := by
  let p := harmonicPolynomialRepresentativeL sphereFischerInner k a
  have hp := harmonicPolynomialRepresentative_mem sphereFischerInner k a
  have hHigh := fixedLowRadialL_high (sphereSobolevSingleL (3/2:ℝ) k a)
  have hLift := fixedHarmonicLift_single k a
  have hRad := outwardRadialTrace_homogeneous k p hp.1
  have hS := congrArg (fun U : BallSobolev 2 => outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U) hLift
  have hEval := polynomialSphereL2_harmonicPolynomialRepresentative sphereFischerInner k a
  have hZ := congrArg (fun z : SphereL2 => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics z)
    (hS.trans (hRad.trans (congrArg (fun z : SphereL2 => (k:ℝ) • z) hEval)))
  have hNorm : sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics ((k:ℝ) • (a:SphereL2)) =
      (k:ℝ) • sphereSobolevSingleL 0 k a :=
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).map_smul (k:ℝ) _).trans
      (congrArg (fun z : SphereSobolev 0 => (k:ℝ) • z) (zeroEquiv_harmonic_subtype k a))
  have hIn := congrArg fixedLowRadialL (sphereSobolevInclusionL_single (3/2:ℝ) (1/2:ℝ) (by norm_num) k a)
  exact hIn.symm.trans (hHigh.trans (congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) (hZ.trans hNorm)))

/-- The genuine flat weak DN map restricts to the usual degree operator on
    the H1 boundary domain. -/
theorem fixedLowRadialL_degree_compatible :
    fixedLowRadialL.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) =
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp sphereSobolevDegreeL := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  exact (congrArg fixedLowRadialL (sphereSobolevInclusionL_single 1 (1/2:ℝ) (by norm_num) k a)).trans
    ((fixedLowRadialL_single k a).trans (congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevDegreeL_single k a).symm))

theorem sphereSobolevDegreeL_symmetric (u v : SphereSobolev 1) :
    ⟪sphereSobolevDegreeL u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,sphereSobolevDegreeL v⟫_ℝ :=
  conormal_midpoint_symmetric fixedLowRadialL sphereSobolevDegreeL fixedLowRadialL_degree_compatible.symm
    fixedLowRadial_symmetric u v

theorem norm_sphereSobolevDegreeL_le_two : ‖sphereSobolevDegreeL‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖sphereSobolevBesselEquiv 1 1 u-sphereSobolevInclusionL 1 0 (by norm_num) u‖ ≤ 2*‖u‖
  have hI : ‖sphereSobolevInclusionL 1 0 (by norm_num) u‖ ≤ ‖u‖ :=
    ((sphereSobolevInclusionL 1 0 (by norm_num)).le_opNorm u).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (norm_nonneg _)).trans_eq (one_mul _))
  exact (norm_sub_le _ _).trans ((add_le_add (LinearIsometryEquiv.norm_map (sphereSobolevBesselEquiv 1 1) u).le hI).trans_eq (by ring))

end ShrinkingSpheres
