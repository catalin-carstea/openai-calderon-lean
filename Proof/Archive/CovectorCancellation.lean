/- The finite slot cancellation from the supplied FiniteCovectorTransport.lean. -/
import Proof.Archive.AngularCoefficient

noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.FiniteCovectorTransport
open AngularPolynomial

lemma fischer_covector_slot_cancellation (w : Fin 3 → Fin 3 → ℝ)
    (hw : ∀ a i,w a i = -w i a) (U V Q Z : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin 3,
      (fischerInner (Q i-∑ a : Fin 3, C (w a i) * U a) (V i) +
      fischerInner (U i) (Z i-∑ a : Fin 3, C (w a i) * V a))) =
      ∑ i : Fin 3, (fischerInner (Q i) (V i)+fischerInner (U i) (Z i)) := by
  have hnegL (p q : MvPolynomial (Fin 3) ℝ) : fischerInner (-p) q = -fischerInner p q := by
    simpa using fischerInner_C_mul_left (-1) p q
  have hnegR (p q : MvPolynomial (Fin 3) ℝ) : fischerInner p (-q) = -fischerInner p q := by
    simpa using fischerInner_C_mul_right (-1) p q
  have hsL (p q r : MvPolynomial (Fin 3) ℝ) : fischerInner (p-q) r = fischerInner p r-fischerInner q r := by
    simp only [sub_eq_add_neg,fischerInner_add_left,hnegL]
  have hsR (p q r : MvPolynomial (Fin 3) ℝ) : fischerInner p (q-r) = fischerInner p q-fischerInner p r := by
    simp only [sub_eq_add_neg,fischerInner_add_right,hnegR]
  have hd (a : Fin 3) : w a a=0 := by have h:=hw a a;linarith
  simp only [hsL,hsR,fischerInner_sum_left,fischerInner_sum_right,
    fischerInner_C_mul_left,fischerInner_C_mul_right,Fin.sum_univ_three,
    fischerInner_add_left,fischerInner_add_right]
  rw [hd 0,hd 1,hd 2,hw 1 0,hw 2 0,hw 2 1]
  ring


end OAI.AnisotropicCalderon.FiniteCovectorTransport
