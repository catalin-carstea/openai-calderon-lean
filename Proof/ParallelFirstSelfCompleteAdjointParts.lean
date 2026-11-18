import Proof.ParallelFirstSelfErrorCoordinateAdjointPacket
import Proof.ParallelFirstSelfCorrectionCoordinateAdjointJet
import Proof.FirstCovariantCoordinateAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma adjoint_three_sub_scalar_inclusion
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (T M C E : V →L[ℝ] V) (w : ℝ) (hT : T.adjoint=T) :
    (M+C+E-w • T).adjoint=M.adjoint+C.adjoint+E.adjoint-w • T := by
  rw [map_sub,map_add,map_add,map_smul,hT]

private lemma model_remainder_higher_graph
    {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I0 : V →L[ℝ] V) (J : H →L[ℝ] V)
    (F M C E : V →L[ℝ] V) (HF HC HE : H →L[ℝ] V) (w : ℝ)
    (hF : I0.comp HF=F.comp J) (hC : I0.comp HC=C.comp J) (hE : I0.comp HE=E.comp J)
    (hSplit : F=M+C+E-w • I0) :
    I0.comp (HF-HC-HE+w • J)=M.comp J := by
  rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_smul,hF,hC,hE,hSplit,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.add_comp,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp]
  module

lemma complete_first_adjoint_low_split
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT) (b : I) (x : X) :
    (P.firstCovariantCoordinateHalfL b x).adjoint=
      (principalModelCoordinateHalfL d x b).adjoint+
      (principalFirstCorrectionCoordinateHalfL d x b).adjoint+
      (P.first.principalFirstErrorCoordinateHalfL x b).adjoint-
      scalarPrincipalConnectionWeight d b x • sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) := by
  have hSplit : P.firstCovariantCoordinateHalfL b x=
      principalModelCoordinateHalfL d x b+principalFirstCorrectionCoordinateHalfL d x b+
      P.first.principalFirstErrorCoordinateHalfL x b-
      scalarPrincipalConnectionWeight d b x • sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) :=
    congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T-scalarPrincipalConnectionWeight d b x • sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (P.firstDerivativeCoordinateHalfL_correction_split x b)
  exact (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T.adjoint) hSplit).trans
    (adjoint_three_sub_scalar_inclusion
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) _ _ _ _
      sphereSobolevHalfNegativeInclusion_adjoint)

/-- Derive the model component's HIGH representative from the SAME WF
and the two already fixed other components. No new model family is selected. -/
def completeAdjointModelHigherFamily
    {Y : Set X} {d : Data} {CF CT CB CS CE ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (E : FirstSelfCoordinateErrorAdjointPacket P CE ε)
    (b : I) (x : X) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  WF.covariantCoordinateAdjointHigher b x-correctionCoordinateAdjointHigherL d b x-E.higher b x+
    scalarPrincipalConnectionWeight d b x • sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)

lemma completeAdjointModelHigherFamily_graph
    {Y : Set X} {d : Data} {CF CT CB CS CE ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (E : FirstSelfCoordinateErrorAdjointPacket P CE ε)
    (b : I) {y : X} (hy : y ∈ Y)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (completeAdjointModelHigherFamily WF E b y)=
      (principalModelCoordinateHalfL d y b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  exact model_remainder_higher_graph
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (P.firstCovariantCoordinateHalfL b y).adjoint (principalModelCoordinateHalfL d y b).adjoint
    (principalFirstCorrectionCoordinateHalfL d y b).adjoint (P.first.principalFirstErrorCoordinateHalfL y b).adjoint
    (WF.covariantCoordinateAdjointHigher b y) (correctionCoordinateAdjointHigherL d b y) (E.higher b y)
    (scalarPrincipalConnectionWeight d b y)
    (WF.covariantCoordinateAdjointHigher_balanced b hy)
    (correctionCoordinateAdjointHigherL_graph d y hFrame b) (E.graph b y hy)
    (complete_first_adjoint_low_split P b y)

lemma completeAdjointHigherFamily_split
    {Y : Set X} {d : Data} {CF CT CB CS CE ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (E : FirstSelfCoordinateErrorAdjointPacket P CE ε) (b : I) :
    WF.covariantCoordinateAdjointHigher b=
      fun x => completeAdjointModelHigherFamily WF E b x+correctionCoordinateAdjointHigherL d b x+
        E.higher b x-scalarPrincipalConnectionWeight d b x •
          sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by
  funext x
  unfold completeAdjointModelHigherFamily
  module

end ShrinkingSpheres.ParallelEnergy
