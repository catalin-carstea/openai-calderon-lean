import Proof.ActualMidpointRadialUniqueness
import Proof.FlatHarmonicBoundaryGradient
import Proof.ConormalRadialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity

lemma RealizesActualMidpointRadialError.full_high (d : Data) (y : X)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hR : RealizesActualMidpointRadialError d y R)
    (F : SmoothCoefficientMatrix 2)
    (hF : ∀ z ∈ (ballOpens : Set X),coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z)
    (f : SphereSobolev (3/2:ℝ)) :
    (R+sphereSobolevDegreeL) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL F f)) := by
  have h := congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => T f) (hR F hF)
  change R (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (fixedHalfOutwardTraceL (strongPoissonL F f)-fixedHalfOutwardTraceL (fixedHarmonicLiftL f)) at h
  rw [map_sub] at h
  have hOut := OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevInclusionL_nativeHalfOutwardTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus
      fixedUnitBallValueTrace (strongPoissonL F f)
  have hFlat := OAI.AnisotropicCalderon.NativeFullHalfRadialTrace.sphereSobolevInclusionL_nativeHalfOutwardTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedSobolevCalculus
      fixedUnitBallValueTrace (fixedHarmonicLiftL f)
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (fixedHalfOutwardTraceL (strongPoissonL F f)) = _ at hOut
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (fixedHalfOutwardTraceL (fixedHarmonicLiftL f)) = _ at hFlat
  rw [hOut,hFlat] at h
  simpa only [_root_.add_apply,sphereSobolevDegreeL_harmonicLift] using
    (congrArg (fun u => u+sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (fixedHarmonicLiftL f))) h).trans
        (sub_add_cancel _ _)

lemma continuousLinearMap_eq_of_high_restriction
    (R T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (h : ∀ f : SphereSobolev (3/2:ℝ),R (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
      T (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) : R = T := by
  apply ContinuousLinearMap.ext
  intro u
  exact (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)).induction_on u
    (isClosed_eq R.continuous T.continuous) h

lemma normalCoefficientJet_value_congr_sphere (F G : SmoothCoefficientMatrix 2)
    (hFG : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val)
    (w : UnitSphere) : coefficientValue 2 (normalCoefficientJet F) w.val =
      coefficientValue 2 (normalCoefficientJet G) w.val := by
  rw [coefficientValue_normalCoefficientJet,coefficientValue_normalCoefficientJet]
  change (∑ i : I,∑ j : I,w.val i*coefficientMatrixField 2 F w.val i j*w.val j) =
    ∑ i : I,∑ j : I,w.val i*coefficientMatrixField 2 G w.val i j*w.val j
  rw [hFG w]

lemma tangentCoefficientJet_value_congr_sphere (F G : SmoothCoefficientMatrix 2)
    (hFG : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val)
    (j : I) (w : UnitSphere) : coefficientValue 2 (tangentCoefficientJet F j) w.val =
      coefficientValue 2 (tangentCoefficientJet G j) w.val := by
  rw [coefficientValue_tangentCoefficientJet,coefficientValue_tangentCoefficientJet]
  change (∑ i : I,w.val i*coefficientMatrixField 2 F w.val i j)-
    (∑ i : I,∑ k : I,w.val i*coefficientMatrixField 2 F w.val i k*w.val k)*w.val j =
    (∑ i : I,w.val i*coefficientMatrixField 2 G w.val i j)-
      (∑ i : I,∑ k : I,w.val i*coefficientMatrixField 2 G w.val i k*w.val k)*w.val j
  rw [hFG w]

lemma conormalRadialL_congr_sphere (F G : SmoothCoefficientMatrix 2)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hFG : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val) :
    conormalRadialL F N = conormalRadialL G N := by
  have hN : smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)) =
      smoothSphereValue (coefficientSmoothData (normalCoefficientJet G)) := by
    ext w
    exact normalCoefficientJet_value_congr_sphere F G hFG w
  have hT (j : I) : smoothSphereValue (coefficientSmoothData (tangentCoefficientJet F j)) =
      smoothSphereValue (coefficientSmoothData (tangentCoefficientJet G j)) := by
    ext w
    exact tangentCoefficientJet_value_congr_sphere F G hFG j w
  simp only [conormalRadialL,coarseBoundaryTangentialL,hN,hT]

/-- The conormal map can be recovered from its actual radial response,
    using the same physical normal and tangential coefficients. -/
lemma conormal_reconstruct_from_radial (F : SmoothCoefficientMatrix 2)
    (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPos : ∀ w : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet F) w.val) :
    (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp
      (conormalRadialL F N)+coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j) = N := by
  let C := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))
  let T := coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  have hC := coarseSphereScalarMulL_isInvertible_of_pos
    (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))) hPos
  apply ContinuousLinearMap.ext
  intro u
  change C (C.inverse (N u-T u))+T u = N u
  rw [hC.self_apply_inverse]
  abel

/-- Uniqueness of the physical H1-to-L2 adjoint through the dense H1 inclusion. -/
lemma radial_physical_adjoint_unique (D A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hA : ∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A v⟫_ℝ)
    (hB : ∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,B v⟫_ℝ) : A = B := by
  apply ContinuousLinearMap.ext
  intro v
  apply (denseRange_sphereSobolevInclusionL 1 0 (by norm_num)).eq_of_inner_right ℝ
  intro u
  exact (hA u v).symm.trans (hB u v)

end ShrinkingSpheres
