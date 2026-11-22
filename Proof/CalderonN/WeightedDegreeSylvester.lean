module

public import Proof.CalderonN.FiniteHilbertDegreeSylvester

import Mathlib.Tactic

/-! Reweight the checked balanced Sylvester estimate to apply to any
pair of dual angular orders. The same finite degrees enter both sides. -/

public section

noncomputable section
open scoped InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3900000
namespace OAI.AnisotropicCalderon.SpectralSylvester

variable {E : ℕ → Type*} [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℝ (E k)]

private theorem weighted_degree_reweight (s a : ℝ) (J : Finset ℕ) (u : ∀ k, E k)
    :
    (∑ k ∈ J, (1+(k:ℝ))^(2*s)*‖(1+(k:ℝ))^a • u k‖^2) =
      ∑ k ∈ J, (1+(k:ℝ))^(2*(s+a))*‖u k‖^2 := by
  apply Finset.sum_congr rfl
  intro k _
  let b : ℝ := 1+(k:ℝ)
  have hb : 0 < b := by dsimp only [b]; positivity
  change b^(2*s)*‖b^a • u k‖^2 = b^(2*(s+a))*‖u k‖^2
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hb.le _),mul_pow,
    ← Real.rpow_two,← Real.rpow_mul hb.le,← mul_assoc,← Real.rpow_add hb]
  congr 2
  ring

theorem finite_hilbert_degree_weighted_form_bound
    (J : Finset ℕ) (K : ∀ m n : ℕ, E n →ₗ[ℝ] E m)
    (shift B s : ℝ) (hShift : (1/2 : ℝ) ≤ shift) (hB : 0 ≤ B)
    (hCasimir : ∀ x y : ∀ k, E k,
      |∑ m ∈ J, ∑ n ∈ J,
        ((((m:ℝ)+shift)^2-((n:ℝ)+shift)^2)*⟪K m n (x n),y m⟫_ℝ)| ≤
      B*Real.sqrt (∑ k ∈ J, (1+(k:ℝ))^(2*(s+1/2))*‖x k‖^2)*
        Real.sqrt (∑ k ∈ J, (1+(k:ℝ))^(2*(-s+1/2))*‖y k‖^2))
    (u v : ∀ k, E k) :
    |∑ m ∈ J, ∑ n ∈ J, ((m:ℝ)-(n:ℝ))*⟪K m n (u n),v m⟫_ℝ| ≤
      2*B*(1+shift)*Real.sqrt (∑ k ∈ J, (1+(k:ℝ))^(2*s)*‖u k‖^2)*
        Real.sqrt (∑ k ∈ J, (1+(k:ℝ))^(2*(-s))*‖v k‖^2) := by
  let bx (k : ℕ) := (1+(k:ℝ))^(1/2-s)
  let by' (k : ℕ) := (1+(k:ℝ))^(1/2+s)
  let K' (m n : ℕ) := (bx n*by' m) • K m n
  have hK (x y : ∀ k, E k) (m n : ℕ) :
      ⟪K' m n (x n),y m⟫_ℝ = ⟪K m n (bx n • x n),by' m • y m⟫_ℝ := by
    simp only [K',LinearMap.smul_apply,map_smul,real_inner_smul_left,real_inner_smul_right]
    ring
  have hC' (x y : ∀ k, E k) :
      |∑ m ∈ J, ∑ n ∈ J, ((((m:ℝ)+shift)^2-((n:ℝ)+shift)^2)*⟪K' m n (x n),y m⟫_ℝ)| ≤
        B*Real.sqrt (∑ k ∈ J, (1+(k:ℝ))^2*‖x k‖^2)*
          Real.sqrt (∑ k ∈ J, (1+(k:ℝ))^2*‖y k‖^2) := by
    simp_rw [hK]
    have h := hCasimir (fun k => bx k • x k) (fun k => by' k • y k)
    dsimp only [bx,by'] at h
    rw [weighted_degree_reweight (s+1/2) (1/2-s) J x,
      weighted_degree_reweight (-s+1/2) (1/2+s) J y] at h
    rw [show 2*(s+1/2+(1/2-s)) = (2:ℝ) by ring,show 2*(-s+1/2+(1/2+s)) = (2:ℝ) by ring] at h
    simpa only [Real.rpow_two] using h
  let x (k : ℕ) := (1+(k:ℝ))^(s-1/2) • u k
  let y (k : ℕ) := (1+(k:ℝ))^(-s-1/2) • v k
  have hx (k : ℕ) : bx k • x k = u k := by
    simp only [bx,x,smul_smul]
    rw [← Real.rpow_add (by positivity),show 1/2-s+(s-1/2) = (0:ℝ) by ring,Real.rpow_zero,one_smul]
  have hy (k : ℕ) : by' k • y k = v k := by
    simp only [by',y,smul_smul]
    rw [← Real.rpow_add (by positivity),show 1/2+s+(-s-1/2) = (0:ℝ) by ring,Real.rpow_zero,one_smul]
  have h := finite_hilbert_degree_half_form_bound J K' shift B hShift hB hC' x y
  simp_rw [hK,hx,hy] at h
  dsimp only [x,y] at h
  have hX := weighted_degree_reweight (1/2) (s-1/2) J u
  have hY := weighted_degree_reweight (1/2) (-s-1/2) J v
  rw [show 2*((1/2:ℝ)+(s-1/2)) = 2*s by ring] at hX
  rw [show 2*((1/2:ℝ)+(-s-1/2)) = 2*(-s) by ring] at hY
  simp only [show 2*(1/2:ℝ) = 1 by norm_num,Real.rpow_one] at hX hY
  rwa [hX,hY] at h

end OAI.AnisotropicCalderon.SpectralSylvester
