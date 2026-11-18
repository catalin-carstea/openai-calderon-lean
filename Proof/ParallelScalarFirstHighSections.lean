import Proof.ParallelScalarFirstIntegrability
import Proof.SupportedHalfCovariantSections
import Proof.ScalarCovariantAdjointDefect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

/-- A genuine first covariant derivative of the already selected H5/2
section, before its lower representatives are taken. -/
def fiveHalfCovariantDerivative (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (a : X) :
    X → SphereSobolev (3/2:ℝ) := fun y => gradedSphereSectionCovariantDerivative (5/2:ℝ) d U y a

lemma fiveHalfCovariantDerivative_inclusion (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (fiveHalfCovariantDerivative d U a y)=
      highSectionCovariantDerivative d (fiveHalfToTwoSection U) y a := by
  have hh := gradedSphereSectionCovariantDerivative_inclusion (5/2:ℝ) 2 (by norm_num) d U y a hU
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  rw [gradedSphereSectionCovariantDerivative_two] at hh
  change sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
      (gradedSphereSectionCovariantDerivative (5/2:ℝ) d U y a)=
    highSectionCovariantDerivative d (fun x => sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) (U x)) y a
  exact hh

lemma fiveHalfCovariantDerivative_half_inclusion (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U a y)=
      halfSectionCovariantDerivativeL d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y a := by
  have hh := gradedSphereSectionCovariantDerivative_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) d U y a hU
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  simpa only [fiveHalfCovariantDerivative,gradedSphereSectionCovariantDerivative_threeHalf] using hh

lemma gradedSphereSectionCovariantDerivative_one (d : Data) (U : X → SphereSobolev 1) (y a : X) :
    gradedSphereSectionCovariantDerivative 1 d U y a=oneSectionCovariantDerivative d U y a := by
  have hI : sphereSobolevInclusionL 1 ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 0 (by norm_num) := by congr 1 <;> norm_num
  simp only [gradedSphereSectionCovariantDerivative,oneSectionCovariantDerivative,hI]

lemma fiveHalfCovariantDerivative_second_inclusion {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    {y : X} (hy : y ∈ Y) (a b : X) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U b) y a)=
      oneSectionCovariantDerivative d
        (fun x => highSectionCovariantDerivative d (fiveHalfToTwoSection U) x b) y a := by
  have hH : ContDiffOn ℝ ∞ (fiveHalfCovariantDerivative d U b) Y :=
    contDiffOn_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU.contDiffOn b
  have hh := gradedSphereSectionCovariantDerivative_inclusion (3/2:ℝ) 1 (by norm_num) d
    (fiveHalfCovariantDerivative d U b) y a ((hH.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hh
  have hSame : (fun x => sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
      (fiveHalfCovariantDerivative d U b x))=
      fun x => highSectionCovariantDerivative d (fiveHalfToTwoSection U) x b :=
    funext (fun x => fiveHalfCovariantDerivative_inclusion d U x b (hU.differentiable (by simp) x))
  rw [hSame] at hh
  simpa only [gradedSphereSectionCovariantDerivative_threeHalf,gradedSphereSectionCovariantDerivative_one] using hh

def scalarFiveHalfSecondSection (d : Data) (A : MetricField) (U : X → SphereSobolev (5/2:ℝ))
    (y : X) : SphereSobolev (1/2:ℝ) :=
  ∑ i : I,∑ j : I,A y i j •
    halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U (axis j)) y (axis i)

def scalarFiveHalfDefectSection (d : Data) (mu : X → ℝ) (A : MetricField)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev (1/2:ℝ) :=
  adjointZeroCoefficient axis mu A y • sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y)+
    ∑ i : I,adjointFirstCoefficient axis mu A y i •
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
        (fiveHalfCovariantDerivative d U (axis i) y)

lemma scalarFiveHalfSecondSection_inclusion {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (A : MetricField) (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (scalarFiveHalfSecondSection d A U y)=
      scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y := by
  simp only [scalarFiveHalfSecondSection,scalarCovariantSecondSection,map_sum,map_smul,
    fiveHalfCovariantDerivative_second_inclusion hY d hg hK he U hU hy]

lemma scalarFiveHalfDefectSection_inclusion (d : Data) (mu : X → ℝ) (A : MetricField)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) (y : X) :
    sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (scalarFiveHalfDefectSection d mu A U y)=
      scalarCovariantAdjointDefectSection d mu A (fiveHalfToTwoSection U) y := by
  simp only [scalarFiveHalfDefectSection,scalarCovariantAdjointDefectSection,map_sum,map_add,map_smul]
  have hFirst (i : I) := congrArg (sphereSobolevInclusionL 1 0 (by norm_num))
    (fiveHalfCovariantDerivative_inclusion d U y (axis i) (hU.differentiable (by simp) y))
  simp only [sphereSobolevInclusionL_trans_apply] at hFirst
  simp only [hFirst,fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply]

end ShrinkingSpheres.ParallelEnergy
