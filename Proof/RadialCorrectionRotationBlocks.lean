import Proof.RadialCorrectionSobolev
import Proof.Archive.RotationCasimir
import Proof.Archive.SphereElementaryCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory MvPolynomial
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection OAI.AnisotropicCalderon.HarmonicDerivativeOperator

theorem polynomialRotation_pderiv_commutator (i j k : I) (p : MvPolynomial I ℝ) :
    polynomialRotation i j (pderiv k p)-pderiv k (polynomialRotation i j p) =
      (if k=j then pderiv i p else 0)-(if k=i then pderiv j p else 0) := by
  simp only [polynomialRotation,map_sub,pderiv_mul,pderiv_X,Pi.single_apply]
  rw [pderiv_pderiv_comm k j,pderiv_pderiv_comm k i]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num

/-- The elementary rotation/derivative commutator on genuine harmonic blocks. -/
theorem harmonicRotation_derivative_commutator (m : ℕ) (i j k : I)
    (a : harmonicSphereSubspace (m+1)) :
    harmonicSphereRotation m i j (harmonicDerivative sphereFischerInner m k a)-
      harmonicDerivative sphereFischerInner m k (harmonicSphereRotation (m+1) i j a) =
        (if k=j then harmonicDerivative sphereFischerInner m i a else 0)-
          (if k=i then harmonicDerivative sphereFischerInner m j a else 0) := by
  obtain ⟨p,rfl⟩ := harmonicPolynomialSphereMap_surjective (m+1) a
  let dp : harmonicHomogeneous m := ⟨pderiv k p,pderiv_harmonicHomogeneous_succ m k p p.property⟩
  let rp : harmonicHomogeneous (m+1) := ⟨polynomialRotation i j p,
    OAI.AnisotropicCalderon.RotationCasimir.polynomialRotation_harmonic_all (m+1) i j p p.property⟩
  have hD : harmonicDerivative sphereFischerInner m k (harmonicPolynomialSphereMap (m+1) p) =
      harmonicPolynomialSphereMap m dp := harmonicDerivative_apply_image sphereFischerInner m k p
  have hR : harmonicSphereRotation (m+1) i j (harmonicPolynomialSphereMap (m+1) p) =
      harmonicPolynomialSphereMap (m+1) rp := harmonicSphereRotation_apply_image (m+1) i j p
  rw [hD,hR,harmonicSphereRotation_apply_image,harmonicDerivative_apply_image,
    harmonicDerivative_apply_image,harmonicDerivative_apply_image]
  apply Subtype.ext
  have h := congrArg polynomialSphereL2 (polynomialRotation_pderiv_commutator i j k p)
  split_ifs at h ⊢ <;>
    simpa only [dp,rp,rotatedHarmonicSphereMap,harmonicPolynomialDerivativeMap,
      LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_sub,ZeroMemClass.coe_zero,map_sub,map_zero] using h

def rotationCovector (q : X →L[ℝ] ℝ) (i j : I) : X →L[ℝ] ℝ :=
  q (axis j) • EuclideanSpace.proj (𝕜:=ℝ) i-q (axis i) • EuclideanSpace.proj (𝕜:=ℝ) j

/-- Exact finite-block rotation covariance of the first radial correction. -/
theorem harmonicRotation_radialDriftBlock_commutator (m : ℕ) (i j : I)
    (q : X →L[ℝ] ℝ) (a : harmonicSphereSubspace (m+1)) :
    harmonicSphereRotation m i j (radialDriftBlockL sphereFischerInner (radialCorrectionVector q) m a)-
      radialDriftBlockL sphereFischerInner (radialCorrectionVector q) m (harmonicSphereRotation (m+1) i j a) =
        radialDriftBlockL sphereFischerInner (radialCorrectionVector (rotationCovector q i j)) m a := by
  let c := -(2*((m+1:ℕ):ℝ)+1)⁻¹
  change harmonicSphereRotation m i j (c • ∑ k : I,(radialCorrectionVector q) k • harmonicDerivative sphereFischerInner m k a)-
      c • ∑ k : I,(radialCorrectionVector q) k • harmonicDerivative sphereFischerInner m k
        (harmonicSphereRotation (m+1) i j a) =
      c • ∑ k : I,(radialCorrectionVector (rotationCovector q i j)) k • harmonicDerivative sphereFischerInner m k a
  rw [map_smul,map_sum,← smul_sub,← Finset.sum_sub_distrib]
  apply congrArg (fun b : harmonicSphereSubspace m => c • b)
  have hTerms (k : I) :
      harmonicSphereRotation m i j ((radialCorrectionVector q) k • harmonicDerivative sphereFischerInner m k a)-
        (radialCorrectionVector q) k • harmonicDerivative sphereFischerInner m k (harmonicSphereRotation (m+1) i j a) =
      (radialCorrectionVector q) k • ((if k=j then harmonicDerivative sphereFischerInner m i a else 0)-
        (if k=i then harmonicDerivative sphereFischerInner m j a else 0)) := by
    rw [map_smul,← smul_sub,harmonicRotation_derivative_commutator]
  simp_rw [hTerms]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.sum_univ_three,radialCorrectionVector,PiLp.toLp_apply,rotationCovector,
      _root_.sub_apply,_root_.smul_apply,PiLp.proj_apply,axis,PiLp.single_apply] <;>
    norm_num <;> module

end ShrinkingSpheres
