import Proof.CoarseAngularProductPackets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace CoarseRotationAdjointPacket

def smul (c : ℝ) (P : CoarseRotationAdjointPacket) : CoarseRotationAdjointPacket where
  operator := c • P.operator
  adjoint := c • P.adjoint
  angular ij := c • P.angular ij
  angularAdjoint ij := c • P.angularAdjoint ij
  pairing := by
    intro u v
    simpa only [_root_.smul_apply,inner_smul_left,inner_smul_right,
      conj_trivial,smul_eq_mul] using congrArg (fun x : ℝ => c*x) (P.pairing u v)
  graph := by
    intro ij f
    simpa only [_root_.smul_apply,map_smul,smul_add,map_add] using
      congrArg (fun x : SphereSobolev (-1) => c • x) (P.graph ij f)
  angularPairing := by
    intro ij u v
    simpa only [_root_.smul_apply,inner_smul_left,inner_smul_right,
      conj_trivial,smul_eq_mul] using congrArg (fun x : ℝ => c*x) (P.angularPairing ij u v)

def add (P Q : CoarseRotationAdjointPacket) : CoarseRotationAdjointPacket where
  operator := P.operator+Q.operator
  adjoint := P.adjoint+Q.adjoint
  angular ij := P.angular ij+Q.angular ij
  angularAdjoint ij := P.angularAdjoint ij+Q.angularAdjoint ij
  pairing := by
    intro u v
    simpa only [_root_.add_apply,inner_add_left,inner_add_right] using congrArg₂
      (fun x y : ℝ => x+y) (P.pairing u v) (Q.pairing u v)
  graph := by
    intro ij f
    simp only [_root_.add_apply,map_add]
    rw [P.graph ij f,Q.graph ij f]
    simp only [map_add]
    abel
  angularPairing := by
    intro ij u v
    simpa only [_root_.add_apply,inner_add_left,inner_add_right] using congrArg₂
      (fun x y : ℝ => x+y) (P.angularPairing ij u v) (Q.angularPairing ij u v)

def sum {κ : Type*} [Fintype κ] (P : κ → CoarseRotationAdjointPacket) : CoarseRotationAdjointPacket where
  operator := ∑ k,(P k).operator
  adjoint := ∑ k,(P k).adjoint
  angular ij := ∑ k,(P k).angular ij
  angularAdjoint ij := ∑ k,(P k).angularAdjoint ij
  pairing := by
    intro u v
    simp only [_root_.sum_apply,sum_inner,inner_sum]
    exact Finset.sum_congr rfl (fun k _ => (P k).pairing u v)
  graph := by
    intro ij f
    simp only [_root_.sum_apply,map_sum]
    calc
      _ = ∑ k,sphereSobolevInclusionL 0 (-1) (by norm_num)
          ((P k).angular ij (sphereSobolevInclusionL 2 1 (by norm_num) f)+
            (P k).operator (sphereSobolevRotationL 2 ij.1 ij.2 f)) :=
        Finset.sum_congr rfl (fun k _ => (P k).graph ij f)
      _ = _ := by simp only [map_add,map_sum,Finset.sum_add_distrib]
  angularPairing := by
    intro ij u v
    simp only [_root_.sum_apply,sum_inner,inner_sum]
    exact Finset.sum_congr rfl (fun k _ => (P k).angularPairing ij u v)

end CoarseRotationAdjointPacket
end ShrinkingSpheres
