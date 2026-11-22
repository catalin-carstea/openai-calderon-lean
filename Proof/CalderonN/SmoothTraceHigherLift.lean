module

public import Proof.CalderonN.SmoothTraceRotationGraph

import Proof.CalderonN.ActualFiniteRadialMidpoint
import Mathlib.Tactic

/-! The rotation graph upgrades the very same trace operator when its
rotation commutators satisfy the corresponding lower-order bounds. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_smoothSphereTraceSobolev_mono (hn : 3 ≤ dim) (s t : ℝ)
    (hs : s ≤ 2) (ht : t ≤ 2) (hst : s ≤ t) (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn s hs u‖ ≤ ‖smoothSphereTraceSobolev hn t ht u‖ := by
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective u
  let w : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  change ‖smoothSphereTraceSobolev hn s hs (smoothSphereTrace w)‖ ≤
    ‖smoothSphereTraceSobolev hn t ht (smoothSphereTrace w)‖
  rw [smoothSphereTraceSobolev_apply,smoothSphereTraceSobolev_apply,
    ← sphereSobolevInclusionL_smoothBoundarySobolev hn t s ht hs hst w]
  exact ((sphereSobolevInclusionL t s hst).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le t s hst) (norm_nonneg _)).trans_eq (one_mul _))

theorem norm_smoothSphereTrace_higher_of_rotation (hn : 3 ≤ dim)
    (s t : ℝ) (hs : s+1 ≤ 2) (ht : t+1 ≤ 2)
    (T : Module.End ℝ (SmoothSphereTrace dim)) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hT : ∀ u, ‖smoothSphereTraceSobolev hn s (by linarith) (T u)‖ ≤
      C*‖smoothSphereTraceSobolev hn t (by linarith) u‖)
    (hK : ∀ (i j : Fin dim) u,
      ‖smoothSphereTraceSobolev hn s (by linarith)
        ((smoothSphereTraceRotation i j*T-T*smoothSphereTraceRotation i j) u)‖ ≤
      D*‖smoothSphereTraceSobolev hn t (by linarith) u‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (s+1) hs (T u)‖ ≤
      Real.sqrt (2*C^2+(dim:ℝ)^2*(D+C*(2*(dim:ℝ)))^2)*
        ‖smoothSphereTraceSobolev hn (t+1) ht u‖ := by
  let B := smoothSphereTraceSobolev hn s (by linarith)
  let L := smoothSphereTraceSobolev hn t (by linarith)
  let H := ‖smoothSphereTraceSobolev hn (t+1) ht u‖
  have hMono : ‖L u‖ ≤ H :=
    norm_smoothSphereTraceSobolev_mono hn t (t+1) (by linarith) ht (by linarith) u
  have hTu : ‖B (T u)‖ ≤ C*H := (hT u).trans (mul_le_mul_of_nonneg_left hMono hC)
  have hKt (i j : Fin dim) : ‖B (smoothSphereTraceRotation i j (T u))‖ ≤ (D+C*(2*(dim:ℝ)))*H := by
    let K := smoothSphereTraceRotation i j
    have hDecompose : K (T u) = (K*T-T*K) u+T (K u) := by
      change K (T u) = K (T u)-T (K u)+T (K u)
      abel
    change ‖B (K (T u))‖ ≤ _
    rw [hDecompose,map_add]
    refine (norm_add_le _ _).trans ?_
    have h₁ : ‖B ((K*T-T*K) u)‖ ≤ D*H :=
      (hK i j u).trans (mul_le_mul_of_nonneg_left hMono hD)
    have h₂ : ‖B (T (K u))‖ ≤ C*((2*(dim:ℝ))*H) :=
      (hT (K u)).trans (mul_le_mul_of_nonneg_left (norm_smoothSphereTraceRotation_le hn t ht i j u) hC)
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  refine (norm_sq_smoothSphereTraceSobolev_le_rotation_graph hn s hs (T u)).trans ?_
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hTerm (i j : Fin dim) :
      ‖B (smoothSphereTraceRotation i j (T u))‖^2 ≤ ((D+C*(2*(dim:ℝ)))*H)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hKt i j) 2
  have hSum :
      (∑ i : Fin dim,∑ j : Fin dim,‖B (smoothSphereTraceRotation i j (T u))‖^2) ≤
        (dim:ℝ)^2*((D+C*(2*(dim:ℝ)))*H)^2 := by
    refine (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))).trans_eq ?_
    simp [pow_two,mul_assoc]
  exact (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hTu 2) (by norm_num))
    hSum).trans_eq (by ring)

end CalderonN
