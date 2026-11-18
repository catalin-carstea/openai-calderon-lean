import Proof.FirstCovariantCoordinateAdjoint
import Proof.PhysicalFirstCoordinateCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma balanced_scalar_drift_commutator {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T Cb Cc : E →L[ℝ] E) (J Bc Ab : H →L[ℝ] E) (wb wc : ℝ)
    (hT : T.adjoint=T) (hC : T.comp Bc=Cc.comp J) (hA : T.comp Ab=Cb.adjoint.comp J) :
    (Cb-wb • T).adjoint.comp (Bc-wc • J)-(Cc-wc • T).comp (Ab-wb • J)=
      Cb.adjoint.comp Bc-Cc.comp Ab := by
  rw [map_sub,map_smul,hT]
  simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_sub,smul_smul,hC,hA]
  module

def PhysicalPrincipalData.firstCovariantCoordinateHigherL {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (b : I) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  P.firstDerivativeCoordinateHigherL x b-scalarPrincipalConnectionWeight d b x •
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)

lemma PhysicalPrincipalData.firstCovariantCoordinateHigherL_balanced
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT) (b : I) (x : X)
    (hB : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL x b)=
      (P.firstDerivativeCoordinateHalfL x b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstCovariantCoordinateHigherL b x)=
      (P.firstCovariantCoordinateHalfL b x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  simp only [PhysicalPrincipalData.firstCovariantCoordinateHigherL,PhysicalPrincipalData.firstCovariantCoordinateHalfL,
    ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.smul_comp,hB]

/-- The actual scalar connection drift leaves the SAME complete angular
commutator row unchanged. Its mixed terms cancel through genuine endpoint
graphs, so no extra frame or drift commutator budget is needed. -/
lemma PhysicalFirstCommutatorPacket.covariantCoordinateCommLow_graph
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (b c : I) {x : X} (hx : x ∈ Y)
    (hB : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL x c)=
      (P.firstDerivativeCoordinateHalfL x c).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (P.firstCovariantCoordinateHalfL b x).adjoint.comp (P.firstCovariantCoordinateHigherL c x)-
      (P.firstCovariantCoordinateHalfL c x).comp (W.covariantCoordinateAdjointHigher b x)=
        (W.coordinateCommLow b c x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hh := balanced_scalar_drift_commutator (E:=SphereSobolev (1/2:ℝ)) (H:=SphereSobolev (3/2:ℝ))
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (P.firstDerivativeCoordinateHalfL x b) (P.firstDerivativeCoordinateHalfL x c)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (P.firstDerivativeCoordinateHigherL x c) (W.coordinateAdjointHigher b x)
    (scalarPrincipalConnectionWeight d b x) (scalarPrincipalConnectionWeight d c x)
    sphereSobolevHalfNegativeInclusion_adjoint hB (W.coordinateAdjointHigher_balanced b hx)
  exact hh.trans (W.coordinateCommLow_graph b c hx)

end ShrinkingSpheres
