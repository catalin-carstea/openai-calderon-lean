import Proof.CanonicalSmoothSobolevSection
import Proof.CovariantOperatorApplication
import Proof.AmbientCovariantCoordinates
import Proof.RightMultiplierRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir

/-- The common H2 section's covariant derivative has exactly the actual
    smooth horizontal L2 representative, through the canonical inclusion. -/
theorem highSectionCovariantDerivative_ambient_coarse (d : Data) (G : X × X → ℝ)
    (hG : ContDiff ℝ ∞ G) (y a : X) :
    sphereSobolevInclusionL 1 0 (by norm_num)
      (highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) G hG) y a)=
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (ambientCovariantL2 G hG y a (frameConnectionCoefficient d.γ d.frame y a)) := by
  let U := ambientSobolevSection 2 (by norm_num) G hG
  let V := ambientSphereL2 G hG
  let I20 := sphereSobolevInclusionL 2 0 (by norm_num)
  let Z : SphereL2 →L[ℝ] SphereSobolev 0 :=
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).toContinuousLinearEquiv.toContinuousLinearMap
  have hUS := (contDiff_ambientSobolevSection 2 (by norm_num) G hG).differentiable (by simp) y
  have hVS := (contDiff_ambientSphereL2 G hG).differentiable (by simp) y
  have hEq : (fun x => I20 (U x))=(fun x => Z (V x)) :=
    funext (ambientSobolevSection_coarse 2 (by norm_num) (by norm_num) G hG)
  have hLeft := I20.hasFDerivAt.comp y hUS.hasFDerivAt
  have hRight := Z.hasFDerivAt.comp y hVS.hasFDerivAt
  have hFD : fderiv ℝ (fun x => I20 (U x)) y=fderiv ℝ (fun x => Z (V x)) y :=
    congrArg (fun F : X → SphereSobolev 0 => fderiv ℝ F y) hEq
  have hDeriv : I20 (fderiv ℝ U y a)=Z (fderiv ℝ V y a) := by
    have hh := congrArg (fun L : X →L[ℝ] SphereSobolev 0 => L a)
      (hLeft.fderiv.symm.trans (hFD.trans hRight.fderiv))
    exact hh
  have hRot (i j : I) : sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevRotationL 2 i j (U y))=
      Z (ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y) := by
    have hh := (sphereSobolevRotationL_one_inclusion_two i j (U y)).symm
    have hU1 : sphereSobolevInclusionL 2 1 (by norm_num) (U y)=ambientSobolevSection 1 (by norm_num) G hG y :=
      ambientSobolevSection_inclusion 2 1 (by norm_num) (by norm_num) (by norm_num) G hG y
    exact hh.trans ((congrArg (sphereSobolevRotationL 1 i j) hU1).trans (ambientSobolevSection_rotation i j G hG y))
  change sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL 2 1 (by norm_num) (fderiv ℝ U y a)-
    ∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) • sphereSobolevRotationL 2 i j (U y))=_
  simp only [map_sub,map_sum,map_smul,hRot]
  have hI : sphereSobolevInclusionL 1 0 (by norm_num)
      (sphereSobolevInclusionL 2 1 (by norm_num) (fderiv ℝ U y a))=I20 (fderiv ℝ U y a) :=
    by
      apply sphereSobolev_ext 0
      intro k
      simp only [sphereSobolevCoefficientL_inclusion,I20]
  rw [hI,hDeriv]
  change Z (fderiv ℝ V y a)-(∑ i : I,∑ j : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
    Z (ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y))=
      Z (ambientCovariantL2 G hG y a (frameConnectionCoefficient d.γ d.frame y a))
  simp only [ambientCovariantL2,map_add,map_sum,map_smul,map_neg,neg_mul,neg_smul,Finset.sum_neg_distrib,sub_eq_add_neg]
  rfl
end ShrinkingSpheres
