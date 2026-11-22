module

/- The finite slot cancellation from the supplied FiniteCovectorTransport.lean. -/
public import Proof.Archive.AngularCoefficient
import Mathlib.Tactic

public section

noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.FiniteCovectorTransport
open AngularPolynomial

variable {n : ℕ}

lemma fischer_covector_slot_cancellation (w : Fin n → Fin n → ℝ)
    (hw : ∀ a i,w a i = -w i a) (U V Q Z : Fin n → MvPolynomial (Fin n) ℝ) :
    (∑ i : Fin n,
      (fischerInner (Q i-∑ a : Fin n, C (w a i) * U a) (V i) +
      fischerInner (U i) (Z i-∑ a : Fin n, C (w a i) * V a))) =
      ∑ i : Fin n, (fischerInner (Q i) (V i)+fischerInner (U i) (Z i)) := by
  have hnegL (p q : MvPolynomial (Fin n) ℝ) : fischerInner (-p) q = -fischerInner p q := by
    simpa using fischerInner_C_mul_left (-1) p q
  have hnegR (p q : MvPolynomial (Fin n) ℝ) : fischerInner p (-q) = -fischerInner p q := by
    simpa using fischerInner_C_mul_right (-1) p q
  have hsL (p q r : MvPolynomial (Fin n) ℝ) : fischerInner (p-q) r = fischerInner p r-fischerInner q r := by
    simp only [sub_eq_add_neg,fischerInner_add_left,hnegL]
  have hsR (p q r : MvPolynomial (Fin n) ℝ) : fischerInner p (q-r) = fischerInner p q-fischerInner p r := by
    simp only [sub_eq_add_neg,fischerInner_add_right,hnegR]
  have hcancel :
      (∑ i, ∑ a, w a i * fischerInner (U a) (V i)) =
        -(∑ i, ∑ a, w a i * fischerInner (U i) (V a)) := by
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun i a => w a i * fischerInner (U a) (V i)), ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun a _ => by rw [hw i a, neg_mul])
  simp only [hsL, hsR, fischerInner_sum_left, fischerInner_sum_right,
    fischerInner_C_mul_left, fischerInner_C_mul_right]
  simp only [sub_add_sub_comm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linear_combination -hcancel

end OAI.AnisotropicCalderon.FiniteCovectorTransport
