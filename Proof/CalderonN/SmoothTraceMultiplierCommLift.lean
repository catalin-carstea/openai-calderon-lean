module

public import Proof.CalderonN.SmoothTraceHigherLift
public import Proof.CalderonN.SmoothTraceDualOrder
public import Proof.CalderonN.SmoothTraceAngularCommutator
public import Proof.CalderonN.FiniteDoubleConormalTrace

import Proof.CalderonN.SmoothTraceMultiplierOrder
import Mathlib.Tactic

/-! The higher multiplier commutator bound reduces to a mixed rotated
commutator on the middle trace space. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2100000
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem commutator_sub_product {R : Type*} [Ring R] (D T M : R) :
    D*(T*M-M*T)-(T*M-M*T)*D =
      ((D*T-T*D)*M-M*(D*T-T*D))+(T*(D*M-M*D)-(D*M-M*D)*T) := by noncomm_ring

theorem norm_smoothTraceMultiplierComm_threeHalf_of_rotated_half (hn : 3 ≤ dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (m : SmoothData dim)
    (C D E : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hHalf : ∀ u,
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) ((T*smoothSphereTraceMul m-smoothSphereTraceMul m*T) u)‖ ≤
        C*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖)
    (hFirst : ∀ (i j : I dim) u,
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num)
        ((smoothTraceAngularComm i j T*smoothSphereTraceMul m-smoothSphereTraceMul m*smoothTraceAngularComm i j T) u)‖ ≤
          D*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖)
    (hSecond : ∀ (i j : I dim) u,
      let m' : SmoothData dim := ⟨sphereRotationDerivative i j m.1,contDiff_sphereRotationDerivative i j m.1 m.2⟩
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) ((T*smoothSphereTraceMul m'-smoothSphereTraceMul m'*T) u)‖ ≤
        E*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) ((T*smoothSphereTraceMul m-smoothSphereTraceMul m*T) u)‖ ≤
      smoothTraceRotationLiftConstant dim C (D+E)*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖ := by
  let M := smoothSphereTraceMul m
  let Q := T*M-M*T
  let P := smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num)
  have hRot (i j : I dim) (v : SmoothSphereTrace dim) :
      ‖P (smoothTraceAngularComm i j Q v)‖ ≤ (D+E)*‖P v‖ := by
    let R := smoothSphereTraceRotation i j
    let m' : SmoothData dim := ⟨sphereRotationDerivative i j m.1,contDiff_sphereRotationDerivative i j m.1 m.2⟩
    have hM : R*M-M*R = smoothSphereTraceMul m' := smoothSphereTraceMul_rotation_comm m i j
    change ‖P ((R*(T*M-M*T)-(T*M-M*T)*R) v)‖ ≤ _
    rw [commutator_sub_product R T M,hM,LinearMap.add_apply,map_add]
    exact (norm_add_le _ _).trans ((add_le_add (hFirst i j v) (hSecond i j v)).trans_eq
      (add_mul D E ‖P v‖).symm)
  have h := norm_smoothSphereTrace_higher_of_rotation hn (1/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
    Q C (D+E) hC (add_nonneg hD hE) hHalf hRot u
  have he : (1/2:ℝ)+1=3/2 := by norm_num
  rw [smoothSphereTraceSobolev_order_eq hn he _ (by norm_num),
    smoothSphereTraceSobolev_order_eq hn he _ (by norm_num)] at h
  exact h

theorem norm_smoothTraceMultiplierComm_negThreeHalf_of_threeHalf (hn : 3 ≤ dim)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (hT : SmoothTraceAdjoint hn T T) (m : SmoothData dim)
    (C : ℝ) (hC : 0 ≤ C)
    (hHigh : ∀ u,
      ‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) ((T*smoothSphereTraceMul m-smoothSphereTraceMul m*T) u)‖ ≤
        C*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (-(3/2):ℝ) (by norm_num) ((T*smoothSphereTraceMul m-smoothSphereTraceMul m*T) u)‖ ≤
      C*‖smoothSphereTraceSobolev hn (-(3/2):ℝ) (by norm_num) u‖ := by
  let M := smoothSphereTraceMul m
  let Q := T*M-M*T
  have hM := smoothSphereTraceMul_symmetric hn m
  have hAdj : SmoothTraceAdjoint hn (-Q) Q := by
    have he : -Q = M*T-T*M := by dsimp only [Q]; abel
    rw [he]
    exact (hM.mul hT).sub (hT.mul hM)
  refine norm_smoothTrace_adjoint_of_bound hn (3/2:ℝ) (3/2:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (-Q) Q hAdj C hC ?_ u
  intro v
  simpa only [LinearMap.neg_apply,map_neg,norm_neg] using hHigh v

end CalderonN
