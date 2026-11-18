/- The four coefficient-contraction lemmas from the selected ZIP's
   lean/Calderon/HessianContraction.lean, preceding metricFrame_square_sum. -/
import Proof.Archive.FischerContraction

noncomputable section
namespace OAI.AnisotropicCalderon.HessianContraction
open AngularPolynomial MvPolynomial

lemma fischerInner_eq_sum_of_support_subset (p q : MvPolynomial (Fin 3) ℝ)
    (s : Finset (Fin 3 →₀ ℕ)) (hp : p.support ⊆ s) :
    fischerInner p q = ∑ a ∈ s, p.coeff a * q.coeff a * fischerWeight a := by
  classical
  unfold fischerInner
  apply Finset.sum_subset hp
  intro a ha hap
  simp [notMem_support_iff.mp hap]

def polynomialFamilySupport (q : Fin 3 → MvPolynomial (Fin 3) ℝ) : Finset (Fin 3 →₀ ℕ) :=
  Finset.univ.biUnion fun i => (q i).support

lemma support_subset_polynomialFamilySupport (q : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (i : Fin 3) : (q i).support ⊆ polynomialFamilySupport q := by
  classical
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,ha⟩

lemma fischer_matrix_contraction_eq_coeff_sum (H : Fin 3 → Fin 3 → ℝ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, H i j * fischerInner (q i) (q j)) =
      ∑ a ∈ polynomialFamilySupport q, fischerWeight a *
        (∑ i : Fin 3, ∑ j : Fin 3, H i j * (q i).coeff a * (q j).coeff a) := by
  classical
  simp_rw [fischerInner_eq_sum_of_support_subset _ _ (polynomialFamilySupport q)
    (support_subset_polynomialFamilySupport q _), Finset.mul_sum]
  have hswap (i : Fin 3) :
      (∑ j : Fin 3, ∑ a ∈ polynomialFamilySupport q,
        H i j * ((q i).coeff a * (q j).coeff a * fischerWeight a)) =
      ∑ a ∈ polynomialFamilySupport q, ∑ j : Fin 3,
        H i j * ((q i).coeff a * (q j).coeff a * fischerWeight a) :=
    Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma sum_fischerInner_self_eq_coeff_sum (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, fischerInner (q i) (q i)) =
      ∑ a ∈ polynomialFamilySupport q, fischerWeight a *
        (∑ i : Fin 3, ((q i).coeff a)^2) := by
  classical
  simp_rw [fischerInner_eq_sum_of_support_subset _ _ (polynomialFamilySupport q)
    (support_subset_polynomialFamilySupport q _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma fischer_matrix_contraction_le_of_quadratic (H : Fin 3 → Fin 3 → ℝ)
    (a : ℝ) (hH : ∀ c : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, H i j * c i * c j) ≤ -a * (∑ i : Fin 3, (c i)^2))
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, H i j * fischerInner (q i) (q j)) ≤
      -a * (∑ i : Fin 3, fischerInner (q i) (q i)) := by
  classical
  rw [fischer_matrix_contraction_eq_coeff_sum, sum_fischerInner_self_eq_coeff_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have h := mul_le_mul_of_nonneg_left (hH (fun i => (q i).coeff b))
    (fischerWeight_pos b).le
  convert h using 1 <;> ring


end OAI.AnisotropicCalderon.HessianContraction
