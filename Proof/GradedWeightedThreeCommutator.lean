import Proof.GradedWeightedThreeCrossCommutator
import Proof.GradedEndpointCommutatorBound
import Proof.ActualFrameFirstAdjointError
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

lemma graded_weighted_three_commutator (I0 : Hi →L[ℝ] Mid)
    (G : I → Mid →L[ℝ] Lo) (Gh : I → Hi →L[ℝ] Mid)
    (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hComm : ∀ i j,GradedEndpointCommutatorBound I0 (G i) (G j) (Gh i) (Gh j) B)
    (u v : I → ℝ) (hu : ∀ i,|u i| ≤ K) (hv : ∀ j,|v j| ≤ K) :
    GradedEndpointCommutatorBound I0 (∑ i,u i • G i) (∑ j,v j • G j)
      (∑ i,u i • Gh i) (∑ j,v j • Gh j) (9*K^2*B) :=
  graded_weighted_three_cross_commutator I0 G G Gh Gh B K hB hK hComm u v hu hv
end ShrinkingSpheres
