import Proof.CanonicalCovariantSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.SmoothAmbientAngularCasimir OAI.AnisotropicCalderon.SmoothMovingFrameFields

lemma sphereSobolevRotation_zero_ambient (i j : I) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevRotationL 0 i j
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 G hG y))=
    sphereSobolevInclusionL 0 (-1) (by norm_num)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) y)) := by
  apply sphereSobolev_ext (-1)
  intro k
  let u := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 G hG y)
  have hCoeff := sphereSobolevCoefficientL_rotation 0 i j k u
  have hOrder : sphereSobolevCoefficientL ((0:ℝ)-1) k (sphereSobolevRotationL 0 i j u)=
      sphereSobolevCoefficientL (-1) k (sphereSobolevRotationL 0 i j u) :=
    congrArg (fun t : ℝ => sphereSobolevCoefficientL t k (sphereSobolevRotationL 0 i j u)) (by norm_num : (0:ℝ)-1= -1)
  have hC := hOrder.symm.trans hCoeff
  change sphereSobolevCoefficientL (-1) k (sphereSobolevRotationL 0 i j u)= _
  rw [hC,sphereSobolevCoefficientL_inclusion]
  simp only [u,sphereSobolevCoefficientL_zeroEquiv]
  exact (sphereHarmonicCoordinate_ambientAngularRotation orthogonalSphereHarmonics denseSphereHarmonics k i j G hG y).symm

lemma coarseSectionCovariantDerivative_congr_germ (d : Data) (y a : X) (U V : X → SphereSobolev 0)
    (h : U =ᶠ[𝓝 y] V) : coarseSectionCovariantDerivative d U y a=coarseSectionCovariantDerivative d V y a := by
  have hP : U y=V y := h.eq_of_nhds
  have hD : fderiv ℝ U y=fderiv ℝ V y := h.fderiv_eq
  simp only [coarseSectionCovariantDerivative,hP,hD]

lemma coarseSectionCovariantDerivative_ambient (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y a : X) :
    coarseSectionCovariantDerivative d (fun x => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (ambientSphereL2 G hG x)) y a=
    sphereSobolevInclusionL 0 (-1) (by norm_num)
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (ambientCovariantL2 G hG y a (frameConnectionCoefficient d.γ d.frame y a))) := by
  let Z : SphereL2 →L[ℝ] SphereSobolev 0 :=
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).toContinuousLinearEquiv.toContinuousLinearMap
  have hD := Z.hasFDerivAt.comp y
    ((contDiff_ambientSphereL2 G hG).differentiable (by simp) y).hasFDerivAt
  have hPoint : fderiv ℝ (fun x => Z (ambientSphereL2 G hG x)) y a=Z (fderiv ℝ (ambientSphereL2 G hG) y a) :=
    congrArg (fun L : X →L[ℝ] SphereSobolev 0 => L a) hD.fderiv
  change fderiv ℝ (fun x => sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
      (ambientSphereL2 G hG x)) y a=
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (fderiv ℝ (ambientSphereL2 G hG) y a) at hPoint
  unfold coarseSectionCovariantDerivative
  rw [hPoint]
  simp only [sphereSobolevRotation_zero_ambient,ambientCovariantL2,map_add,map_sum,map_smul,map_neg,
    neg_mul,neg_smul,Finset.sum_neg_distrib,sub_eq_add_neg]
end ShrinkingSpheres
