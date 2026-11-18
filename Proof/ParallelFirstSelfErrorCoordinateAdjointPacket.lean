import Proof.UniformPrincipalFirstErrorCoordinateData
import Proof.ParallelFirstSelfErrorWeightedJetPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One fixed HIGH true-adjoint family for the COMPLETE weighted actual
native-error coordinate coefficient, selected before all directions/tests. -/
structure FirstSelfCoordinateErrorAdjointPacket
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT) (CE ε : ℝ) where
  higher : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  low_smooth : ∀ b,ContDiffOn ℝ ∞ (fun x => (P.first.principalFirstErrorCoordinateHalfL x b).adjoint) Y
  graph : ∀ b y,y ∈ Y →
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (higher b y)=
      (P.first.principalFirstErrorCoordinateHalfL y b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  norm : ∀ b y,y ∈ Y → ‖higher b y‖ ≤ CE*ε/beta d.γ d.radius y
  jet : ∀ b i y,y ∈ Y → ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    halfOperatorCovariantDerivativeL d (fun x => (P.first.principalFirstErrorCoordinateHalfL x b).adjoint)
      (higher b) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧ ‖H‖ ≤ CE*ε

lemma actual_error_coordinate_adjoint_eq
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (Lo : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {x : X} (hx : x ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (hLo : ∀ a,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) x)=
        (Lo a x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) (b : I) :
    (P.first.principalFirstErrorCoordinateHalfL x b).adjoint=
      ∑ a : I,principalFirstErrorCoordinateWeight d a b x • (Lo a x).adjoint := by
  rw [P.first.principalFirstErrorCoordinateHalfL_eq Lo hx hFrame hLo b]
  simp only [Fin.sum_univ_three,LinearIsometryEquiv.map_add,LinearIsometryEquiv.map_smulₛₗ,
    starRingEnd_apply,star_trivial,principalFirstErrorCoordinateWeight]

end ShrinkingSpheres.ParallelEnergy
