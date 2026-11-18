import Proof.PhysicalCorrectionCoframeEndpoints
import Proof.FirstErrorCoordinateContraction
import Proof.PrincipalFirstErrorCoordinateWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def principalFirstCorrectionCoordinateHalfL (d : Data) (y : X) (b : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  d.radius y • (∑ j : I,d.frame y j b • (∑ i : I,
    (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i) • firstFrameLowerCorrectionL d y i))

def principalFirstCorrectionCoordinateHigherL (d : Data) (y : X) (b : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ a : I,principalFirstErrorCoordinateWeight d a b y • physicalFirstCorrectionHigherL d y (axis a)

/-- Both moving frame indices cancel before the small scalar profile
    weights are differentiated. -/
lemma principalFirstCorrectionCoordinateHalfL_eq (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (b : I) :
    principalFirstCorrectionCoordinateHalfL d y b=
      ∑ a : I,principalFirstErrorCoordinateWeight d a b y • physicalFirstCorrectionHalfL d y (axis a) := by
  have hF (i : I) : firstFrameLowerCorrectionL d y i=
      ∑ a : I,d.frame y i a • physicalFirstCorrectionHalfL d y (axis a) :=
    (physicalFirstCorrectionHalfL_frame d y hFrame i).symm.trans
      (physicalFirstCorrectionHalfL_axis_expansion d y (d.frame y i))
  unfold principalFirstCorrectionCoordinateHalfL
  simp only [hF]
  rw [frameTensor_operator_coordinate_contraction d.γ d.frame y hFrame]
  simp only [Finset.smul_sum,smul_smul,principalFirstErrorCoordinateWeight]

lemma PhysicalPrincipalData.firstDerivativeCoordinateHalfL_correction_split
    {Y : Set X} {d : Data} {CF CT : ℝ} (D : PhysicalPrincipalData Y d CF CT) (y : X) (b : I) :
    D.firstDerivativeCoordinateHalfL y b=
      (∑ j : I,d.frame y j b • principalModelFirstDerivativeHalfL d y j)+
      principalFirstCorrectionCoordinateHalfL d y b+D.first.principalFirstErrorCoordinateHalfL y b :=
  D.firstDerivativeCoordinateHalfL_split y b
end ShrinkingSpheres
