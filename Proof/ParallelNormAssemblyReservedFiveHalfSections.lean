import Proof.ParallelNormAssemblyReservedQuadraticPair
import Proof.SupportedHalfCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma graded_covariant_derivative_five_half (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y a : X) :
    gradedSphereSectionCovariantDerivative (5/2:ℝ) d U y a=fiveHalfSectionCovariantDerivativeL d U y a := by
  have hI : sphereSobolevInclusionL (5/2:ℝ) ((5/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simp only [gradedSphereSectionCovariantDerivative,fiveHalfSectionCovariantDerivativeL,
    frameAngularConnectionFiveHalfL,hI,_root_.sum_apply,_root_.smul_apply]

lemma contDiff_supported_five_half_covariant_derivative {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (a : X) :
    ContDiff ℝ ∞ (fun x => fiveHalfSectionCovariantDerivativeL d U x a) ∧
      ∀ x ∉ S,fiveHalfSectionCovariantDerivativeL d U x a=0 := by
  have hh := contDiff_supported_gradedSphereSectionCovariantDerivative hY (5/2:ℝ) d hg hK he U hU S hS hSY h0 a
  simpa only [graded_covariant_derivative_five_half] using hh

lemma five_half_covariant_derivative_to_half (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y a)=
      halfSectionCovariantDerivativeL d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y a := by
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  have hh := gradedSphereSectionCovariantDerivative_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) d U y a hU
  rw [hI,graded_covariant_derivative_five_half,gradedSphereSectionCovariantDerivative_threeHalf] at hh
  exact hh

lemma five_half_covariant_derivative_to_coarse (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y a)=
      highSectionCovariantDerivative d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) (U x)) y a := by
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) := by congr 1 <;> norm_num
  have hh := gradedSphereSectionCovariantDerivative_inclusion (5/2:ℝ) 2 (by norm_num) d U y a hU
  rw [hI,graded_covariant_derivative_five_half,gradedSphereSectionCovariantDerivative_two] at hh
  exact hh

end ShrinkingSpheres.ParallelEnergy
