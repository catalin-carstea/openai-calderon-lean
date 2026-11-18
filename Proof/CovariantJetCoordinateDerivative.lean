import Proof.CovariantThirdCoordinateExpansion
import Proof.ThirdTensorFrameBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma contDiffOn_covJet {Y : Set X} (hY : IsOpen Y) (g : MetricField) (f : X → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y)
    (hΓ : ∀ a b c : I,ContDiffOn ℝ ∞ (fun x => christoffel g x a b c) Y)
    (n : ℕ) (idx : Fin n → I) : ContDiffOn ℝ ∞ (fun y => covJet g f n y idx) Y := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    change ContDiffOn ℝ ∞ (fun y =>
      coordDeriv (idx 0) (fun x => covJet g f n x (Fin.tail idx)) y-
        ∑ t : Fin n,∑ k : I,christoffel g y k (idx 0) (idx t.succ)*
          covJet g f n y (Function.update (Fin.tail idx) t k)) Y
    exact (contDiffOn_coordDeriv hY (ih (Fin.tail idx)) (idx 0)).sub
      (ContDiffOn.sum (fun t ht => ContDiffOn.sum (fun k hk =>
        (hΓ k (idx 0) (idx t.succ)).mul (ih (Function.update (Fin.tail idx) t k)))))

lemma coordDeriv_covJet_cons (g : MetricField) (f : X → ℝ) (n : ℕ) (y : X) (i : I) (idx : Fin n → I) :
    coordDeriv i (fun x => covJet g f n x idx) y =
      covJet g f (n+1) y (Fin.cons i idx)+
        ∑ t : Fin n,∑ k : I,christoffel g y k i (idx t)*covJet g f n y (Function.update idx t k) := by
  simp only [covJet,Fin.cons_zero,Fin.tail_cons,Fin.cons_succ]
  ring

lemma abs_coordDeriv_covJet_le (g : MetricField) (f : X → ℝ) (n : ℕ) (y : X)
    (β G B C : ℝ) (hβ : 1 ≤ β) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hΓ : ∀ a b c : I,|christoffel g y a b c| ≤ G)
    (hT : ∀ idx : Fin n → I,|covJet g f n y idx| ≤ B*β^n)
    (hNext : ∀ idx : Fin (n+1) → I,|covJet g f (n+1) y idx| ≤ C*β^(n+1))
    (i : I) (idx : Fin n → I) :
    |coordDeriv i (fun x => covJet g f n x idx) y| ≤ (C+3*n*G*B)*β^(n+1) := by
  have hβ0 := zero_le_one.trans hβ
  have hTerm (t : Fin n) (k : I) :
      |christoffel g y k i (idx t)*covJet g f n y (Function.update idx t k)| ≤ G*B*β^n := by
    rw [abs_mul]
    exact (mul_le_mul (hΓ k i (idx t)) (hT (Function.update idx t k)) (abs_nonneg _) hG).trans_eq (by ring)
  have hSum : |∑ t : Fin n,∑ k : I,christoffel g y k i (idx t)*covJet g f n y (Function.update idx t k)| ≤
      3*n*G*B*β^n := by
    calc
      _ ≤ ∑ t : Fin n,|∑ k : I,christoffel g y k i (idx t)*covJet g f n y (Function.update idx t k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t : Fin n,∑ k : I,|christoffel g y k i (idx t)*covJet g f n y (Function.update idx t k)| :=
        Finset.sum_le_sum (fun t ht => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _t : Fin n,∑ _k : I,G*B*β^n := Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun k hk => hTerm t k))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  rw [coordDeriv_covJet_cons]
  have hPower : β^n ≤ β^(n+1) := pow_le_pow_right₀ hβ (by omega)
  calc
    _ ≤ |covJet g f (n+1) y (Fin.cons i idx)|+
        |∑ t : Fin n,∑ k : I,christoffel g y k i (idx t)*covJet g f n y (Function.update idx t k)| := abs_add_le _ _
    _ ≤ C*β^(n+1)+3*n*G*B*β^n := add_le_add (hNext _) hSum
    _ ≤ C*β^(n+1)+3*n*G*B*β^(n+1) := by gcongr
    _ = _ := by ring
end ShrinkingSpheres
