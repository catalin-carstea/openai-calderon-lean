import Proof.FirstPoissonPolynomial
import Proof.Archive.SphereSobolevRadialDrift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory MvPolynomial
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SpectralCoreRegularity OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open OAI.AnisotropicCalderon.GreenRadialTrace
open OAI.AnisotropicCalderon.SphereHilbertDecomposition OAI.AnisotropicCalderon.SpectralWeightedGraph

/-- The first normal radial correction is a bounded operator of order zero. -/
def coarseFirstRadialVariationL (c : ℝ) (L : X →L[ℝ] ℝ) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  c⁻¹ • ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      (WithLp.toLp 2 (fun i => L (axis i)))).comp
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.toContinuousLinearEquiv.toContinuousLinearMap))

lemma zeroEquiv_harmonic_subtype (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (a : SphereL2) =
      sphereSobolevSingleL 0 k a := by
  change sphereHarmonicDecomposition orthogonalSphereHarmonics denseSphereHarmonics (a : SphereL2) = _
  rw [sphereHarmonicDecomposition_subtype]
  simp only [sphereSobolevSingleL,besselWeight_zero_order,ContinuousLinearMap.smul_apply,
    lp.singleContinuousLinearMap_apply,one_smul]

/-- Quantitative order-zero norm bound in terms of the same center scalar
    and affine covector used in the actual coefficient Taylor model. -/
theorem norm_coarseFirstRadialVariationL_le (c : ℝ) (L : X →L[ℝ] ℝ) :
    ‖coarseFirstRadialVariationL c L‖ ≤ 6*|c⁻¹| * ‖L‖ := by
  have hSum : ∑ i : I,|L (axis i)| ≤ 3*‖L‖ := by
    have hi (i : I) : |L (axis i)| ≤ ‖L‖ := by
      simpa only [Real.norm_eq_abs,norm_axis,mul_one] using L.le_opNorm (axis i)
    rw [Fin.sum_univ_three]
    nlinarith only [hi 0,hi 1,hi 2]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  change ‖c⁻¹ • sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    (radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      (WithLp.toLp 2 (fun i => L (axis i)))
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm f))‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,LinearIsometryEquiv.norm_map]
  have hT := norm_radialDriftTraceL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (WithLp.toLp 2 (fun i => L (axis i)))
  have hNorm := (radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (WithLp.toLp 2 (fun i => L (axis i)))).le_opNorm
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm f)
  rw [LinearIsometryEquiv.norm_map] at hNorm
  have hb := hNorm.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have hc := mul_le_mul_of_nonneg_left hb (abs_nonneg c⁻¹)
  have hSum' : (∑ i : I,|(WithLp.toLp 2 (fun i => L (axis i))) i|) ≤ 3*‖L‖ := hSum
  exact hc.trans ((show |c⁻¹| *((2*∑ i : I,|(WithLp.toLp 2 (fun i => L (axis i))) i|)*‖f‖) ≤
      |c⁻¹| *((2*(3*‖L‖))*‖f‖) by gcongr).trans_eq (by ring))

/-- Exact identification of the actual high first variation with the bounded
    order-zero radial drift operator. This uses dense finite harmonic data. -/
theorem highFirstRadialVariation_coarse_eq (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : c ≠ 0) (L : X →L[ℝ] ℝ)
    (hF0 : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ (ballOpens : Set X),∀ i j,coefficientValue 2 (F1 i j) x = L x*(1:Mat) i j)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (highFirstRadialVariationL F0 F1 c) =
      (coarseFirstRadialVariationL c L).comp (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)) := by
  let T := (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (highFirstRadialVariationL F0 F1 c)
  let R := (coarseFirstRadialVariationL c L).comp (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num))
  have hSingle (k : ℕ) (a : harmonicSphereSubspace k) :
      T (sphereSobolevSingleL (3/2:ℝ) k a) = R (sphereSobolevSingleL (3/2:ℝ) k a) := by
    let p := harmonicPolynomialRepresentativeL sphereFischerInner k a
    have hp := harmonicPolynomialRepresentative_mem sphereFischerInner k a
    have hLift := fixedHarmonicLift_single k a
    have hZ := zeroEquiv_harmonic_subtype k a
    have hR : R (sphereSobolevSingleL (3/2:ℝ) k a) = c⁻¹ •
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
          (radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
            (WithLp.toLp 2 (fun i => L (axis i))) (a : SphereL2)) := by
      change coarseFirstRadialVariationL c L
        (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (sphereSobolevSingleL (3/2:ℝ) k a)) = _
      rw [sphereSobolevInclusionL_single,← hZ]
      change c⁻¹ • sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics _
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (a : SphereL2)))) = _
      rw [LinearIsometryEquiv.symm_apply_apply]
    rw [hR]
    cases k with
    | zero =>
      have hpC : p = C (p.coeff 0) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous I).mpr hp.1)
      have hP := strongFirstPoissonVariation_polynomial F0 F1 c hc L hF0 hF1 hInv p hp.1 hp.2 _ hLift
      rw [hpC,driftFirstVariation_C] at hP
      have hP0 : strongFirstPoissonVariationL F0 F1 c (sphereSobolevSingleL (3/2:ℝ) 0 a) = 0 :=
        hP.trans (by change c⁻¹ • polynomialBallSobolevLinearMap 2 0 = 0;rw [map_zero,smul_zero])
      change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (fixedHalfOutwardTraceL
        (strongFirstPoissonVariationL F0 F1 c (sphereSobolevSingleL (3/2:ℝ) 0 a))) = _
      rw [hP0,map_zero,map_zero,radialDriftTraceL_constant,map_zero,smul_zero]
    | succ m =>
      let q : harmonicHomogeneous (m+1) := ⟨p,hp⟩
      have h := firstRadialVariation_polynomial F0 F1 c hc L hF0 hF1 hInv m q _ hLift
      rw [polynomialSphereL2_harmonicPolynomialRepresentative] at h
      exact h
  apply ContinuousLinearMap.ext
  have hEq : (T : SphereSobolev (3/2:ℝ) → SphereSobolev 0) = R :=
    denseRange_harmonicBoundaryFiniteL.equalizer T.continuous R.continuous (by
      funext a
      change T (harmonicBoundaryFiniteL a) = R (harmonicBoundaryFiniteL a)
      rw [harmonicBoundaryFiniteL_eq_sum,map_sum,map_sum]
      exact Finset.sum_congr rfl (fun k _ => hSingle k (a k)))
  exact congr_fun hEq

end ShrinkingSpheres
