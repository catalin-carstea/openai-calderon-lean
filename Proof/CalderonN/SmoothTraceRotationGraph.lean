module

public import Proof.CalderonN.SmoothSphereTrace
public import Proof.CalderonN.HarmonicRotationCasimir

import Proof.CalderonN.ActualFiniteRadialMidpoint
import Mathlib.Tactic

/-! The Casimir graph norm on the same smooth trace core controls one
additional angular derivative in every fixed dimension. -/

public section

noncomputable section
open Set
open scoped ContDiff ENNReal InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothSphereTraceSobolev_coordinate (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (u : SmoothSphereTrace dim) (k : ℕ) :
    smoothSphereTraceSobolev hn s hs u k =
      besselWeight s k • harmonicProjection k (smoothSphereTraceL2 hn u) := by
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective u
  let w : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  change smoothSphereTraceSobolev hn s hs (smoothSphereTrace w) k =
    besselWeight s k • harmonicProjection k (smoothSphereTraceL2 hn (smoothSphereTrace w))
  rw [smoothSphereTraceSobolev_apply,smoothSphereTraceL2_apply,smoothBoundarySobolev_apply]

theorem smoothSphereTraceSobolev_rotate_coordinate (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (i j : Fin dim) (u : SmoothSphereTrace dim) (k : ℕ) :
    smoothSphereTraceSobolev hn s hs (smoothSphereTraceRotation i j u) k =
      harmonicSphereRotation k i j (smoothSphereTraceSobolev hn s hs u k) := by
  obtain ⟨v,rfl⟩ := smoothSphereTraceL_surjective u
  let w : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  change smoothSphereTraceSobolev hn s hs (smoothSphereTraceRotation i j (smoothSphereTrace w)) k =
    harmonicSphereRotation k i j (smoothSphereTraceSobolev hn s hs (smoothSphereTrace w) k)
  rw [smoothSphereTraceRotation_apply,smoothSphereTraceSobolev_coordinate,smoothSphereTraceSobolev_coordinate,
    smoothSphereTraceL2_apply,smoothSphereTraceL2_apply,harmonicProjection_sphereRotationDerivative,map_smul]

theorem smoothSphereTraceSobolev_succ_coordinate (hn : 3 ≤ dim) (s : ℝ) (hs : s+1 ≤ 2)
    (u : SmoothSphereTrace dim) (k : ℕ) :
    smoothSphereTraceSobolev hn (s+1) hs u k =
      (1+(k:ℝ)) • smoothSphereTraceSobolev hn s (by linarith) u k := by
  rw [smoothSphereTraceSobolev_coordinate,smoothSphereTraceSobolev_coordinate,smul_smul]
  congr 1
  unfold besselWeight
  rw [Real.rpow_add (by positivity),Real.rpow_one,mul_comm]

private theorem sum_norm_sq_sphereSobolev_le (s : ℝ) (u : SphereSobolev dim s) (t : Finset ℕ) :
    (∑ k ∈ t,‖u k‖^2) ≤ ‖u‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.sum_rpow_le_norm_rpow
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u t

private theorem norm_sq_sphereSobolev_le_of_partial (s : ℝ) (u : SphereSobolev dim s)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ t : Finset ℕ,(∑ k ∈ t,‖u k‖^2) ≤ C) :
    ‖u‖^2 ≤ C := by
  have hN := lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (Real.sqrt_nonneg C) (f := u) (fun t => by
      simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.sq_sqrt hC]
      exact h t)
  exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans_eq (Real.sq_sqrt hC)

theorem norm_sq_smoothSphereTraceSobolev_le_rotation_graph (hn : 3 ≤ dim) (s : ℝ) (hs : s+1 ≤ 2)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (s+1) hs u‖^2 ≤
      2*‖smoothSphereTraceSobolev hn s (by linarith) u‖^2+
      ∑ i : Fin dim,∑ j : Fin dim,‖smoothSphereTraceSobolev hn s (by linarith)
        (smoothSphereTraceRotation i j u)‖^2 := by
  let T := smoothSphereTraceSobolev hn s (by linarith)
  apply norm_sq_sphereSobolev_le_of_partial
  · positivity
  intro t
  have hPoly (k : ℕ) : (1+(k:ℝ))^2 ≤ 2+2*(k:ℝ)*((k:ℝ)+dim-2) := by
    have hd : (3:ℝ) ≤ dim := by exact_mod_cast hn
    nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (show (0:ℝ) ≤ dim-3 by linarith),
      sq_nonneg (k:ℝ)]
  have hTerm (k : ℕ) : ‖smoothSphereTraceSobolev hn (s+1) hs u k‖^2 ≤
      2*‖T u k‖^2+∑ i : Fin dim,∑ j : Fin dim,‖T (smoothSphereTraceRotation i j u) k‖^2 := by
    rw [smoothSphereTraceSobolev_succ_coordinate,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),mul_pow]
    change _ ≤ 2*‖T u k‖^2+∑ i : Fin dim,∑ j : Fin dim,
      ‖smoothSphereTraceSobolev hn s (by linarith) (smoothSphereTraceRotation i j u) k‖^2
    simp_rw [smoothSphereTraceSobolev_rotate_coordinate]
    rw [sum_norm_sq_harmonicSphereRotation,← add_mul]
    exact mul_le_mul_of_nonneg_right (hPoly k) (sq_nonneg _)
  refine (Finset.sum_le_sum fun k _ => hTerm k).trans ?_
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
  refine add_le_add (mul_le_mul_of_nonneg_left (sum_norm_sq_sphereSobolev_le s _ t) (by norm_num)) ?_
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ => sum_norm_sq_sphereSobolev_le s _ t

theorem norm_smoothSphereTraceRotation_le (hn : 3 ≤ dim) (s : ℝ) (hs : s+1 ≤ 2)
    (i j : Fin dim) (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn s (by linarith) (smoothSphereTraceRotation i j u)‖ ≤
      (2*(dim:ℝ))*‖smoothSphereTraceSobolev hn (s+1) hs u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  apply norm_sq_sphereSobolev_le_of_partial _ _ _ (sq_nonneg _)
  intro t
  let U := smoothSphereTraceSobolev hn (s+1) hs u
  let V := smoothSphereTraceSobolev hn s (by linarith) (smoothSphereTraceRotation i j u)
  let C := 2*(dim:ℝ)
  have hh (k : ℕ) : ‖V k‖ ≤ C*‖U k‖ := by
    dsimp only [V,U]
    rw [smoothSphereTraceSobolev_rotate_coordinate,smoothSphereTraceSobolev_succ_coordinate,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (by positivity),← mul_assoc]
    exact norm_harmonicSphereRotation_le hn k i j _
  change (∑ k ∈ t,‖V k‖^2) ≤ (C*‖U‖)^2
  calc
    _ ≤ ∑ k ∈ t,(C*‖U k‖)^2 := Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hh k) 2
    _ = C^2*(∑ k ∈ t,‖U k‖^2) := by simp only [mul_pow,Finset.mul_sum]
    _ ≤ C^2*‖U‖^2 :=
      mul_le_mul_of_nonneg_left (sum_norm_sq_sphereSobolev_le _ U t) (sq_nonneg C)
    _ = (C*‖U‖)^2 := by ring

end CalderonN
