module

public import Proof.CalderonN.ZonalReproduction

import Mathlib.Tactic

public section

noncomputable section

namespace CalderonN
open OAI.AnisotropicCalderon.AngularPolynomial

/-- The harmonic multiplicity after one binomial factor is extracted. -/
theorem mul_harmonicMultiplicity {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    ((n : ℝ)-2) * harmonicMultiplicity n k =
      (2*(k : ℝ) + n - 2) * ((n+k-3).choose k : ℝ) := by
  match k with
  | 0 => simp [harmonicMultiplicity]
  | 1 =>
    have h : ((n + 1 - 3 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [show n+1-3 = n-2 by omega, Nat.cast_sub (by omega)]
      norm_num
    simp only [harmonicMultiplicity, Nat.cast_one, Nat.choose_one_right, h]
    ring
  | j+2 =>
    let b := n+j-1
    have hb' : b - (j+1) = n-2 := by dsimp [b]; omega
    have hc : (n+j+1).choose (j+2) =
        b.choose j + (b.choose (j+1) + (b+1).choose (j+2)) := by
      rw [show n+j+1 = (b+1)+1 by dsimp [b]; omega, Nat.choose_succ_succ',
        Nat.choose_succ_succ' b j, Nat.add_assoc]
    have hm : harmonicMultiplicity n (j+2) =
        b.choose (j+2) + 2 * b.choose (j+1) := by
      rw [harmonicMultiplicity, hc, Nat.add_sub_cancel_left, Nat.choose_succ_succ' b (j+1)]
      change b.choose (j+1) + (b.choose (j+1) + b.choose (j+2)) = _
      omega
    have hsel := Nat.choose_succ_right_eq b (j+1)
    rw [hb'] at hsel
    have hsel' :
        (b.choose (j+2) : ℝ) * ((j : ℝ)+2) =
          (b.choose (j+1) : ℝ) * ((n : ℝ)-2) := by
      have hcast : ((n-2 : ℕ) : ℝ) = (n : ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
      have h : (b.choose (j+2) : ℝ) * ((j+2 : ℕ) : ℝ) =
          (b.choose (j+1) : ℝ) * ((n-2 : ℕ) : ℝ) := by exact_mod_cast hsel
      simpa only [Nat.cast_add, Nat.cast_ofNat, hcast] using h
    rw [hm, show n+(j+2)-3 = b by dsimp [b]; omega]
    push_cast
    linear_combination 2 * hsel'.symm

theorem harmonicMultiplicity_succ_mul {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    (harmonicMultiplicity n (k+1) : ℝ) * ((k : ℝ)+1) * (2*(k : ℝ)+n-2) =
      (harmonicMultiplicity n k : ℝ) * (2*(k : ℝ)+n) * ((k : ℝ)+n-2) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (n : ℝ) - 2 ≠ 0 := by linarith
  let b := n+k-3
  have hb : ((b : ℕ) : ℝ)+1 = (k : ℝ)+n-2 := by
    dsimp [b]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hbinom : (((b+1).choose (k+1) : ℕ) : ℝ) * ((k : ℝ)+1) =
      ((k : ℝ)+n-2) * (b.choose k : ℝ) := by
    rw [← hb]
    exact_mod_cast (Nat.add_one_mul_choose_eq b k).symm
  have hnext := mul_harmonicMultiplicity hn (k+1)
  rw [show n+(k+1)-3 = b+1 by dsimp [b]; omega, Nat.cast_add, Nat.cast_one] at hnext
  have hcur := mul_harmonicMultiplicity hn k
  change _ = _ * (b.choose k : ℝ) at hcur
  apply mul_left_cancel₀ hd
  calc
    _ = (((n : ℝ)-2) * harmonicMultiplicity n (k+1)) * ((k : ℝ)+1) *
        (2*(k : ℝ)+n-2) := by ring
    _ = (2*(k : ℝ)+n) * (2*(k : ℝ)+n-2) *
        ((b+1).choose (k+1) * ((k : ℝ)+1)) := by rw [hnext]; ring
    _ = (((n : ℝ)-2) * harmonicMultiplicity n k) * (2*(k : ℝ)+n) *
        ((k : ℝ)+n-2) := by rw [hbinom, hcur]; ring
    _ = _ := by ring

private theorem zonalFischerFactor_succ {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    zonalFischerFactor n (k+1) =
      (((k : ℝ)+1) * (2*(k : ℝ)+n-2) / ((k : ℝ)+n-2)) * zonalFischerFactor n k := by
  cases k with
  | zero =>
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hd : (n : ℝ)-2 ≠ 0 := by linarith
    simp [zonalFischerFactor, hd]
  | succ k =>
    simp only [zonalFischerFactor, Nat.cast_succ]
    congr 1
    ring

/-- The solid zonal reproducing factor times the dimension is exactly the
Fischer-to-sphere normalization. -/
theorem harmonicMultiplicity_mul_zonalFischerFactor {n : ℕ} (hn : 3 ≤ n) (k : ℕ) :
    (harmonicMultiplicity n k : ℝ) * zonalFischerFactor n k = sphereNormalization n k := by
  induction k with
  | zero => simp [harmonicMultiplicity, zonalFischerFactor]
  | succ k ih =>
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hk : (0 : ℝ) ≤ k := by positivity
    have hden : (k : ℝ)+n-2 ≠ 0 := by linarith
    rw [zonalFischerFactor_succ hn, sphereNormalization_succ, ← ih]
    have hm := harmonicMultiplicity_succ_mul hn k
    field_simp [hden]
    linear_combination zonalFischerFactor n k * hm

theorem weighted_normalizedFischer_zonalPolynomial {n : ℕ} (hn : 3 ≤ n)
    (w : I n → ℝ) (k : ℕ) (p : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    (harmonicMultiplicity n k : ℝ) * normalizedFischerInner k (zonalPolynomial w k) p =
      MvPolynomial.eval w p := by
  have hnorm : 0 < sphereNormalization n k := sphereNormalization_pos (by omega) k
  unfold normalizedFischerInner
  rw [Fintype.card_fin, fischerInner_zonalPolynomial w k p hp hΔ, ← mul_div_assoc,
    ← mul_assoc, harmonicMultiplicity_mul_zonalFischerFactor hn]
  exact mul_div_cancel_left₀ _ hnorm.ne'

end CalderonN
