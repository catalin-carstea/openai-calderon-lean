import Proof.CanonicalHorizontalSection
import Proof.LeadingPrincipalModelSection
import Proof.AngularComponentData
import Proof.CanonicalTestSobolevSections
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereFields
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.AngularShiftGraph

lemma ambientSobolevSection_degree (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevDegreeL (ambientSobolevSection 1 (by norm_num) G hG y)=
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientDegreeField G hG y) := by
  apply sphereSobolev_ext 0
  intro k
  rw [sphereSobolevCoefficientL_physicalDegree,ambientSobolevSection_coefficient,
    sphereSobolevCoefficientL_zeroEquiv]
  exact (harmonicProjection_ambientDegree G hG y k).symm

namespace AngularComponentData
variable {Y : Set X} {d : Data} {φ : Field} {L : ℂ →L[ℝ] ℝ}
  {E : HarmonicTestExpansion Y d.γ d.frame φ}

/-- The canonical genuine section in the physical principal decomposition
is exactly the already selected raising model output, including the same
horizontal representative and localized log-radius coefficient. -/
theorem canonical_raising_section_eq (D : AngularComponentData E d.radius L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[nhds z] (fun _ => (1:ℝ)))
    {y : X} (hy : y ∈ Y) :
    let U := ambientSobolevSection 2 (by norm_num) (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth)
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))=D.raisingOutput y := by
  dsimp only
  let G := fun p => L (E.representative p)
  have hG : ContDiff ℝ ∞ G := L.contDiff.comp E.representativeSmooth
  let U := ambientSobolevSection 2 (by norm_num) G hG
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hSource : ∀ x ∈ Y,∀ w : UnitSphere,G (x,w.val)=L (φ (x,frameVector d.frame x w.val)) :=
    fun x hx w => congrArg L (E.representativeEq x hx w)
  have hHorizontal (i : I) : highSectionCovariantDerivative d U y (d.frame y i)=
      ambientSobolevSection 1 (by norm_num) (D.horizontalRepresentative i) (D.horizontalSmooth i) y :=
    canonical_horizontal_oneSection_eq hY d h hK he hFrame φ hφ L G (D.horizontalRepresentative i)
      hG (D.horizontalSmooth i) i hSource (D.horizontalEq i) hy
  have hDegree : sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevShiftedDegreeL 2 (U y))=
      Z (ambientDegreeField G hG y) := by
    rw [sphereSobolevShiftedDegreeL_two_coarse]
    dsimp only [U]
    rw [ambientSobolevSection_inclusion 2 1 (by norm_num) (by norm_num) (by norm_num) G hG y,
      ambientSobolevSection_degree]
  have hCoefficient (i : I) :
      (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) • sphereSobolevShiftedDegreeL 2 (U y)=
        D.coefficient i y • sphereSobolevShiftedDegreeL 2 (U y) := by
    by_cases hs : y ∈ E.supportSet
    · rw [D.coefficientEq i y hs]
    · have hZero : U y=0 := by
        apply ambientSobolevSection_eq_zero_off 2 (by norm_num) G hG E.supportSet _ hs
        intro x hx w
        dsimp only [G]
        rw [E.representativeZero x hx w,map_zero]
      rw [hZero,map_zero,smul_zero,smul_zero]
  have hInput (i : I) : Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) (highSectionModelPlus d U y i))=
      weightedAngularSection (D.horizontalRepresentative i) G (D.horizontalSmooth i) hG (D.coefficient i) 1 y := by
    rw [highSectionModelPlus,hCoefficient i,hHorizontal i,map_add,map_smul,
      ambientSobolevSection_coarse,hDegree,map_add,map_smul,LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]
    simp only [weightedAngularSection,one_smul]
  have hEach (i : I) : Z.symm (flatOneRaisingL i (highSectionModelPlus d U y i))=
      angularRaisingSection i (D.horizontalRepresentative i) G (D.horizontalSmooth i) hG (D.coefficient i) y := by
    have hGraph := coordinateBoundaryGradientAdjointL_graph Q hQ i (highSectionModelPlus d U y i)
    rw [← flatRaisingSobolevL_one Q hQ i] at hGraph
    rw [hInput i] at hGraph
    exact sphereRaisingGraph_output_unique sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
      _ _ _ hGraph (angularRaisingSection_graph i (D.horizontalRepresentative i) G
        (D.horizontalSmooth i) hG (D.coefficient i) y)
  change Z.symm (∑ i : I,flatOneRaisingL i (highSectionModelPlus d U y i))=D.raisingOutput y
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => hEach i)
end AngularComponentData
end ShrinkingSpheres
