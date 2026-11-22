module

public import Proof.CalderonN.SmoothSphereRotationProjection

import Mathlib.Tactic

/-! The harmonic block Casimir calculation from Proposition 5.3
release f308cb9d with eigenvalue k(k+dim−2). -/

public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MvPolynomial
open scoped InnerProductSpace
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial

variable {dim : ℕ} [NeZero dim]

theorem sum_harmonicSphereRotation_twice (k : ℕ) (v : harmonicSphereSubspace dim k) :
    (∑ i : Fin dim, ∑ j : Fin dim,
      harmonicSphereRotation k i j (harmonicSphereRotation k i j v)) =
    (-(2*(k:ℝ)*((k:ℝ)+dim-2))) • v := by
  rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
  have hRot (i j : Fin dim) (q : harmonicHomogeneous dim k) :
      harmonicSphereRotation k i j (harmonicPolynomialSphereMap k q) =
      harmonicPolynomialSphereMap k
        ⟨polynomialRotation i j q,polynomialRotation_harmonic_all k i j q q.property⟩ := by
    rw [harmonicSphereRotation_apply_image]
    rfl
  simp only [hRot]
  apply Subtype.ext
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  change (∑ i : Fin dim, ∑ j : Fin dim,
      polynomialSphereL2 (polynomialRotation i j (polynomialRotation i j p))) =
    (-(2*(k:ℝ)*((k:ℝ)+dim-2))) • polynomialSphereL2 p
  simp_rw [← map_sum]
  have he : (∑ i : Fin dim, ∑ j : Fin dim,
      polynomialRotation i j (polynomialRotation i j p)) =
      C (-(2*(k:ℝ)*((k:ℝ)+dim-2))) * (p : MvPolynomial (Fin dim) ℝ) := by
    calc
      _ = C (-2 : ℝ) * polynomialCasimir p := by
        rw [polynomialCasimir,← mul_assoc,← map_mul]
        norm_num
      _ = _ := by
        rw [polynomialCasimir_harmonic k _ p.property,← mul_assoc,← map_mul]
        congr 2
        ring
  rw [he,← smul_eq_C_mul,map_smul]

theorem sum_norm_sq_harmonicSphereRotation (k : ℕ) (v : harmonicSphereSubspace dim k) :
    ∑ i : Fin dim, ∑ j : Fin dim, ‖harmonicSphereRotation k i j v‖^2 =
      2*(k:ℝ)*((k:ℝ)+dim-2)*‖v‖^2 := by
  have he := congrArg (fun u : harmonicSphereSubspace dim k => -⟪u,v⟫_ℝ)
    (sum_harmonicSphereRotation_twice k v)
  change -(⟪_,v⟫_ℝ) = -(⟪(-(2*(k:ℝ)*((k:ℝ)+dim-2))) • v,v⟫_ℝ) at he
  rw [real_inner_smul_left v v (-(2*(k:ℝ)*((k:ℝ)+dim-2))),
    real_inner_self_eq_norm_sq,neg_mul,neg_neg] at he
  simpa only [sum_inner,inner_harmonicSphereRotation_skew,real_inner_self_eq_norm_sq,
    Finset.sum_neg_distrib,neg_neg,real_inner_smul_left,neg_mul] using he

theorem norm_harmonicSphereRotation_le (hn : 3 ≤ dim) (k : ℕ) (i j : Fin dim)
    (v : harmonicSphereSubspace dim k) :
    ‖harmonicSphereRotation k i j v‖ ≤ (2*(dim:ℝ))*(1+(k:ℝ))*‖v‖ := by
  have hd : (3 : ℝ) ≤ dim := by exact_mod_cast hn
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hBound : 2*(k:ℝ)*((k:ℝ)+dim-2) ≤ ((2*(dim:ℝ))*(1+(k:ℝ)))^2 := by
    have h₁ : (k:ℝ) ≤ 1+k := by linarith
    have h₂ : (k:ℝ)+dim-2 ≤ (dim:ℝ)*(1+k) := by nlinarith [mul_nonneg (by linarith : 0 ≤ (dim:ℝ)) hk]
    have h₃ := mul_le_mul h₁ h₂ (by linarith : 0 ≤ (k:ℝ)+dim-2)
      (by positivity : 0 ≤ 1+(k:ℝ))
    calc
      _ ≤ 2*((1+(k:ℝ))*((dim:ℝ)*(1+k))) := by linarith
      _ = (2*(dim:ℝ))*(1+(k:ℝ))^2 := by ring
      _ ≤ ((2*(dim:ℝ))*(1+(k:ℝ)))^2 := by
        rw [mul_pow]
        have hd₁ : 2*(dim:ℝ) ≤ (2*(dim:ℝ))^2 := by nlinarith
        exact mul_le_mul_of_nonneg_right hd₁ (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ ∑ l : Fin dim, ‖harmonicSphereRotation k i l v‖^2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ l : Fin dim, ∑ m : Fin dim, ‖harmonicSphereRotation k l m v‖^2 :=
      Finset.single_le_sum (f := fun l : Fin dim => ∑ m : Fin dim, ‖harmonicSphereRotation k l m v‖^2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    _ = 2*(k:ℝ)*((k:ℝ)+dim-2)*‖v‖^2 := sum_norm_sq_harmonicSphereRotation k v
    _ ≤ ((2*(dim:ℝ))*(1+(k:ℝ)))^2*‖v‖^2 :=
      mul_le_mul_of_nonneg_right hBound (sq_nonneg _)
    _ = _ := by ring

end CalderonN
