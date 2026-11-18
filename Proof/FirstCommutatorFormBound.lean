import Proof.PhysicalErrorForms
import Proof.Archive.SphereSobolevPairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def firstCommutatorForm
    (S : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (V : I → SphereSobolev (1/2:ℝ)) : ℝ :=
  ∑ i : I,∑ j : I,sphereSobolevDualPairing (1/2:ℝ) (V i) (S i j (V j))

lemma abs_firstCommutatorForm_le
    (S : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (V : I → SphereSobolev (1/2:ℝ)) {C ε β : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hβ : 1 ≤ β)
    (hS : ∀ i j,‖S i j‖ ≤ C*(ε/β)^2) :
    |firstCommutatorForm S V| ≤ (9*C*ε)*(β⁻¹*(∑ i : I,‖V i‖^2)) := by
  have hβ0 : 0 < β := zero_lt_one.trans_le hβ
  have hDiv : 0 ≤ ε/β := div_nonneg hε hβ0.le
  have hDiv1 : ε/β ≤ 1 := (div_le_one hβ0).2 (hε1.trans hβ)
  have hSq : (ε/β)^2 ≤ ε/β := by nlinarith only [mul_nonneg hDiv (sub_nonneg.mpr hDiv1)]
  have hN (i j : I) : ‖S i j‖ ≤ C*ε/β :=
    ((hS i j).trans (mul_le_mul_of_nonneg_left hSq hC)).trans_eq (by ring)
  let N := ∑ i : I,‖V i‖^2
  have hSingle (i : I) : ‖V i‖^2 ≤ N :=
    Finset.single_le_sum (f:=fun k : I => ‖V k‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hProd (i j : I) : ‖V i‖*‖V j‖ ≤ N := by
    nlinarith only [hSingle i,hSingle j,sq_nonneg (‖V i‖-‖V j‖)]
  have hPair (i j : I) : |sphereSobolevDualPairing (1/2:ℝ) (V i) (S i j (V j))| ≤
      (C*ε)*(β⁻¹*N) := by
    rw [sphereSobolevDualPairing,real_inner_comm]
    calc
      _ ≤ (C*ε/β)*‖V j‖*‖V i‖ := abs_inner_apply_le (S i j) (V j) (V i) (hN i j)
      _ = (C*ε/β)*(‖V j‖*‖V i‖) := by ring
      _ ≤ (C*ε/β)*N := mul_le_mul_of_nonneg_left (hProd j i) (div_nonneg (mul_nonneg hC hε) hβ0.le)
      _ = _ := by ring
  calc
    _ ≤ ∑ i : I,∑ j : I,|sphereSobolevDualPairing (1/2:ℝ) (V i) (S i j (V j))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : I,∑ _j : I,(C*ε)*(β⁻¹*N) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hPair i j))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];dsimp only [N];ring
end ShrinkingSpheres
