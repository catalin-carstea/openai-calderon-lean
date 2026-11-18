import Proof.FlatLoweringSobolev
import Proof.CanonicalRaisingSectionOutput

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

def highSectionModelMinus (d : Data) (U : X → SphereSobolev 2) (y : X) (j : I) : SphereSobolev 1 :=
  -highSectionCovariantDerivative d U y (d.frame y j)+
    (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) • sphereSobolevShiftedDegreeL 2 (U y)

namespace AngularComponentData
variable {Y : Set X} {d : Data} {φ : Field} {L : ℂ →L[ℝ] ℝ}
  {E : HarmonicTestExpansion Y d.γ d.frame φ}

/-- The canonical genuine section in the physical principal decomposition
is exactly the already selected lowering model output, including the same
horizontal representative and localized log-radius coefficient. -/
theorem canonical_lowering_section_eq (D : AngularComponentData E d.radius L)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[nhds z] (fun _ => (1:ℝ)))
    {y : X} (hy : y ∈ Y) :
    let U := ambientSobolevSection 2 (by norm_num) (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth)
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (∑ i : I,flatLoweringSobolevL 1 i (highSectionModelMinus d U y i))=D.loweringOutput y := by
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
  have hInput (i : I) : Z.symm (sphereSobolevInclusionL 1 0 (by norm_num) (highSectionModelMinus d U y i))=
      weightedAngularSection (D.horizontalRepresentative i) G (D.horizontalSmooth i) hG (D.coefficient i) (-1) y := by
    rw [highSectionModelMinus,hCoefficient i,hHorizontal i,map_add,map_neg,map_smul,
      ambientSobolevSection_coarse,hDegree,map_add,map_neg,map_smul,LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply]
    simp only [weightedAngularSection,neg_one_smul]
  have hEach (i : I) : Z.symm (flatLoweringSobolevL 1 i (highSectionModelMinus d U y i))=
      angularLoweringSection i (D.horizontalRepresentative i) G (D.horizontalSmooth i) hG (D.coefficient i) y := by
    have hGraph := coordinateBoundaryGradientL_graph Q hQ i (highSectionModelMinus d U y i)
    rw [← flatLoweringSobolevL_one Q hQ i] at hGraph
    rw [hInput i] at hGraph
    exact sphereDerivativeGraph_output_unique sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
      _ _ _ hGraph (angularLoweringSection_graph i (D.horizontalRepresentative i) G
        (D.horizontalSmooth i) hG (D.coefficient i) y)
  change Z.symm (∑ i : I,flatLoweringSobolevL 1 i (highSectionModelMinus d U y i))=D.loweringOutput y
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => hEach i)
end AngularComponentData
end ShrinkingSpheres
