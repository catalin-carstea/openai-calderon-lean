import Proof.ParallelFirstSelfGradedCurvature
import Proof.ParallelFirstSelfBalancedSourceGreen

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

/-- The intrinsic weak covariant derivative of a smooth half source. -/
def weakHalfSourceCovariantDerivative (d : Data) (L : X → SphereSobolev (1/2:ℝ))
    (y a : X) : SphereSobolev (-(1/2:ℝ)) :=
  sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (fderiv ℝ L y a)-
    frameAngularConnectionHalfL d y a (L y)

lemma weakHalfSourceCovariantDerivative_eq_graded (d : Data)
    (L : X → SphereSobolev (1/2:ℝ)) (y a : X) :
    weakHalfSourceCovariantDerivative d L y a=gradedSphereSectionCovariantDerivative (1/2:ℝ) d L y a := by
  simp only [weakHalfSourceCovariantDerivative,gradedSphereSectionCovariantDerivative,
    frameAngularConnectionHalfL,_root_.sum_apply,_root_.smul_apply]
  congr 2
  congr 1 <;> norm_num

lemma balanced_positive_half_derivative_weak_graph (d : Data)
    (L : X → SphereSobolev (1/2:ℝ)) (H : X → SphereSobolev (3/2:ℝ)) (y a : X)
    (hH : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H y)=L y) :
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (balancedPositiveHalfDerivative d L H y a)=weakHalfSourceCovariantDerivative d L y a := by
  have hC := DFunLike.congr_fun (frameAngularConnectionHigherL_compatible d y a) (H y)
  simp only [ContinuousLinearMap.comp_apply,hH] at hC
  simp only [balancedPositiveHalfDerivative,weakHalfSourceCovariantDerivative,map_sub,hC]

lemma balanced_negative_half_derivative_graded_graph (d : Data)
    (V : X → SphereSobolev (-(1/2:ℝ))) (W : X → SphereSobolev (1/2:ℝ)) (y a : X)
    (hW : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W y)=V y) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (balancedNegativeHalfDerivative d V W y a)=
        gradedSphereSectionCovariantDerivative (-(1/2:ℝ)) d V y a := by
  have hR (i j : I) : sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
      (sphereSobolevRotationL (1/2:ℝ) i j (W y))=
        sphereSobolevRotationL (-(1/2:ℝ)) i j (V y) := by
    rw [←hW]
    simpa only [sphereSobolevInclusionL,show (1/2:ℝ)-1= -(1/2:ℝ) by norm_num,
      show (-(1/2:ℝ))-1= -(3/2:ℝ) by norm_num] using
        (sphereSobolevRotationL_inclusion_apply (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) i j (W y)).symm
  simp only [balancedNegativeHalfDerivative,gradedSphereSectionCovariantDerivative,
    frameAngularConnectionHalfL,_root_.sum_apply,_root_.smul_apply,map_sub,map_sum,map_smul,hR]
  congr 2
  congr 1 <;> norm_num

/-- Curvature for smooth LOWER half sources, with arbitrary pointwise
positive-half first-derivative lifts. No lift is differentiated. -/
theorem balanced_weak_half_source_commutator {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (L : X → SphereSobolev (1/2:ℝ)) (hL : ContDiffOn ℝ ∞ L Y)
    (G : X → X → SphereSobolev (1/2:ℝ))
    (hG : ∀ a x,x ∈ Y → sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (G a x)=
      weakHalfSourceCovariantDerivative d L x a)
    {y : X} (hy : y ∈ Y) (a b : X) :
    balancedNegativeHalfDerivative d (fun x => weakHalfSourceCovariantDerivative d L x b) (G b) y a-
      balancedNegativeHalfDerivative d (fun x => weakHalfSourceCovariantDerivative d L x a) (G a) y b=
    frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y a b (L y) := by
  apply sphereSobolevInclusionL_injective (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)
  rw [map_sub,balanced_negative_half_derivative_graded_graph d _ _ y a (hG b y hy),
    balanced_negative_half_derivative_graded_graph d _ _ y b (hG a y hy)]
  have hPoint : ∀ c,(fun x => weakHalfSourceCovariantDerivative d L x c)=
      (fun x => gradedSphereSectionCovariantDerivative (1/2:ℝ) d L x c) :=
    fun c => funext (fun x => weakHalfSourceCovariantDerivative_eq_graded d L x c)
  rw [hPoint b,hPoint a]
  have hComm := half_source_sphere_covariant_commutator hY d hg hK he hFrame L hL hy a b
  have hCurv := DFunLike.congr_fun (frameCurvatureSobolevL_inclusion (1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) d.γ d.frame y a b) (L y)
  simp only [ContinuousLinearMap.comp_apply] at hCurv
  have hD (F : X → SphereSobolev (-(1/2:ℝ))) (v : X) :
      gradedSphereSectionCovariantDerivative ((1/2:ℝ)-1) d F y v=
        gradedSphereSectionCovariantDerivative (-(1/2:ℝ)) d F y v := by congr 1 <;> norm_num
  have hC : frameCurvatureSobolevL ((1/2:ℝ)-1) d.γ d.frame y a b=
      frameCurvatureSobolevL (-(1/2:ℝ)) d.γ d.frame y a b := by congr 1 <;> norm_num
  have hI : sphereSobolevInclusionL (1/2:ℝ) ((1/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  have hOut : sphereSobolevInclusionL ((1/2:ℝ)-1) ((-(1/2:ℝ))-1) (by norm_num)=
      sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  rw [hD,hD,hC,hI] at hComm
  rw [hOut] at hCurv
  exact hComm.trans hCurv.symm

end ShrinkingSpheres.ParallelEnergy
