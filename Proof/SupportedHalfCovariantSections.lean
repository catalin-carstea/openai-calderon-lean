import Proof.GradedSphereSectionCovariantDerivative
import Proof.HalfCanonicalCovariantSection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma gradedSphereSectionCovariantDerivative_threeHalf (d : Data)
    (U : X → SphereSobolev (3/2:ℝ)) (y a : X) :
    gradedSphereSectionCovariantDerivative (3/2:ℝ) d U y a=halfSectionCovariantDerivativeL d U y a := by
  have hI : sphereSobolevInclusionL (3/2:ℝ) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simp only [gradedSphereSectionCovariantDerivative,halfSectionCovariantDerivativeL_apply,
    frameAngularConnectionHigherL,hI,_root_.sum_apply,_root_.smul_apply]

lemma contDiff_supported_halfSectionCovariantDerivative {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (U : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0 : ∀ x ∉ S,U x=0) (a : X) :
    ContDiff ℝ ∞ (fun x => halfSectionCovariantDerivativeL d U x a) ∧
      ∀ x ∉ S,halfSectionCovariantDerivativeL d U x a=0 := by
  have hh := contDiff_supported_gradedSphereSectionCovariantDerivative hY (3/2:ℝ) d hg hK he U hU S hS hSY h0 a
  simpa only [gradedSphereSectionCovariantDerivative_threeHalf] using hh

end ShrinkingSpheres
