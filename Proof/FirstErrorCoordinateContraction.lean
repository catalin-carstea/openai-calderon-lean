import Proof.PhysicalFirstDerivativeCoordinates
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both frame indices cancel in the fixed-coordinate contraction of a
    symmetric tensor weight and a frame-linear operator family. -/
lemma frameTensor_operator_coordinate_contraction {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : MetricField) (e : Frame) (y : X)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (Q : Mat) (F : I → W) (b : I) :
    (∑ j : I,e y j b • (∑ i : I,(frameTensorMatrix g e y Q i j+frameTensorMatrix g e y Q j i) •
      (∑ a : I,e y i a • F a)))=
      ∑ a : I,(Q a b+Q b a) • F a := by
  let q := frameTensorMatrix g e y Q
  have hCoeff (a : I) : (∑ i : I,∑ j : I,(q i j+q j i)*e y i a*e y j b)=Q a b+Q b a := by
    have hSwap : (∑ i : I,∑ j : I,q j i*e y i a*e y j b)=Q b a := by
      calc
        _ = ∑ j : I,∑ i : I,q j i*e y j b*e y i a := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := frameTensorMatrix_reconstruct g e y hFrame Q b a
    simp only [add_mul,Finset.sum_add_distrib]
    rw [frameTensorMatrix_reconstruct g e y hFrame Q a b,hSwap]
  calc
    _ = ∑ a : I,(∑ i : I,∑ j : I,(q i j+q j i)*e y i a*e y j b) • F a := by
      change (∑ j : I,e y j b • (∑ i : I,(q i j+q j i) • (∑ a : I,e y i a • F a)))=_
      simp only [Fin.sum_univ_three]
      module
    _ = _ := by simp only [hCoeff]

namespace ActualFrameErrorEndpointPair
variable {Y : Set X} {d : Data}
  {A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
  {G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {CE : ℝ}

lemma low_eq_axis_combination (P : ActualFrameErrorEndpointPair Y d A G CE)
    (Lo : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {y : X} (hy : y ∈ Y)
    (hLo : ∀ a,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis a) A (G a) y)=
        (Lo a y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) (j : I) :
    P.low j y=∑ a : I,d.frame y j a • Lo a y := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  have hP := DFunLike.congr_fun (P.low_coarse j y hy) u
  have hA (a : I) := DFunLike.congr_fun (hLo a) u
  simp only [ContinuousLinearMap.comp_apply] at hP hA ⊢
  rw [← hP]
  simp only [actualFrameFirstAdjointErrorFamily,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,hA]

def principalFirstErrorCoordinateHalfL (P : ActualFrameErrorEndpointPair Y d A G CE) (y : X) (b : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  d.radius y • (∑ j : I,d.frame y j b • (∑ i : I,
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) • P.low i y))

/-- The actual error contribution to the principal first-base coefficient
    has coordinate weights r(P_ab+P_ba). Thus no derivative of the arbitrary
    frame appears when its scalar jets are estimated. -/
lemma principalFirstErrorCoordinateHalfL_eq (P : ActualFrameErrorEndpointPair Y d A G CE)
    (Lo : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {y : X} (hy : y ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (hLo : ∀ a,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis a) A (G a) y)=
        (Lo a y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) (b : I) :
    P.principalFirstErrorCoordinateHalfL y b=
      ∑ a : I,(d.radius y*(principal d.γ d.g₂ y a b+principal d.γ d.g₂ y b a)) • Lo a y := by
  unfold principalFirstErrorCoordinateHalfL
  simp only [P.low_eq_axis_combination Lo hy hLo]
  rw [frameTensor_operator_coordinate_contraction d.γ d.frame y hFrame]
  simp only [Finset.smul_sum,smul_smul]
end ActualFrameErrorEndpointPair

/-- The coordinate error just identified is the actual first-error part
    of the full physical first-base coefficient. Model and bounded
    geometric correction terms remain explicit for their own estimates. -/
lemma PhysicalPrincipalData.firstDerivativeCoordinateHalfL_split
    {Y : Set X} {d : Data} {CF CT : ℝ} (D : PhysicalPrincipalData Y d CF CT) (y : X) (b : I) :
    D.firstDerivativeCoordinateHalfL y b=
      (∑ j : I,d.frame y j b • principalModelFirstDerivativeHalfL d y j)+
      d.radius y • (∑ j : I,d.frame y j b • (∑ i : I,
        (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
          frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) • firstFrameLowerCorrectionL d y i))+
      D.first.principalFirstErrorCoordinateHalfL y b := by
  simp only [PhysicalPrincipalData.firstDerivativeCoordinateHalfL,PhysicalPrincipalData.firstDerivativeHalfL,
    ActualFrameErrorEndpointPair.principalFirstDerivativeHalfL,
    ActualFrameErrorEndpointPair.principalFirstErrorCoordinateHalfL,smul_add,Finset.sum_add_distrib]
  simp only [Fin.sum_univ_three]
  module
end ShrinkingSpheres
