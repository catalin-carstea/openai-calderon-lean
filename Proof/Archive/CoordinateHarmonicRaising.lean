/- Adopted from the selected ZIP, lean/Calderon/HarmonicCoordinateCompatibility.lean.
   Initial generic coordinateHarmonicRaising definition, equality and harmonicity lemmas only; specialized geometric applications omitted.
-/
import Proof.Archive.SphereAngularCore

set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.HarmonicCoordinateCompatibility
open AngularPolynomial SphereHarmonic

def coordinateHarmonicRaising (k : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := X i * p - C ((2*(k:ℝ)+1)⁻¹) * radiusSq * pderiv i p

lemma coordinateHarmonicRaising_eq_harmonicRaising (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) :
    coordinateHarmonicRaising k i p = harmonicRaising (k-1) (Pi.single i p) := by
  have hcoef : 2 / (4*((k-1:ℕ):ℝ)+2*(Fintype.card (Fin 3):ℝ)) = (2*(k:ℝ)+1)⁻¹ := by
    have hden : 4*((k-1:ℕ):ℝ)+2*(Fintype.card (Fin 3):ℝ) = 2*(2*(k:ℝ)+1) := by
      rw [Nat.cast_sub hk]
      simp only [Nat.cast_one,Fintype.card_fin,Nat.cast_ofNat]
      ring
    rw [hden]
    simp only [div_eq_mul_inv,mul_inv_rev]
    norm_num
    ring
  have hdiv : polynomialDivergence (Pi.single i p) = pderiv i p := by
    simp [polynomialDivergence,Pi.single_apply,apply_ite]
  rw [harmonicRaising,hcoef,hdiv]
  simp [coordinateHarmonicRaising,polynomialRaising,Pi.single_apply]

theorem coordinateHarmonicRaising_harmonicHomogeneous (k : ℕ) (hk : 1 ≤ k) (i : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    coordinateHarmonicRaising k i p ∈ harmonicHomogeneous (k+1) := by
  have hh : ∀ j : Fin 3, ((Pi.single i p : Fin 3 → MvPolynomial (Fin 3) ℝ) j).IsHomogeneous k := by
    intro j
    by_cases hj : j=i
    · subst j;simpa using hp.1
    · have hz : (0 : MvPolynomial (Fin 3) ℝ).IsHomogeneous k :=
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ k).zero_mem
      simpa only [Pi.single_apply,if_neg hj] using hz
  have hl : ∀ j : Fin 3, laplacian ((Pi.single i p : Fin 3 → MvPolynomial (Fin 3) ℝ) j) = 0 := by
    intro j
    by_cases hj : j=i
    · subst j;simpa using hp.2
    · simp [Pi.single_apply,hj,laplacian]
  rw [coordinateHarmonicRaising_eq_harmonicRaising k hk]
  exact ⟨harmonicRaising_isHomogeneous hk _ hh,
    laplacian_harmonicRaising _ hh hl (ne_of_gt (radiusSq_laplacian_coefficient_pos (k-1)))⟩


end OAI.AnisotropicCalderon.HarmonicCoordinateCompatibility
