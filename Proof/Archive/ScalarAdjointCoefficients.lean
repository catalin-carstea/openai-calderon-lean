/- Adopted from the selected ZIP, lean/Calderon/ActualScalarPrincipalAdjoint.lean.
   Selected generic declarations only; proof bodies preserved, local imports narrowed. -/
import Proof.Archive.ScalarDensityAdjoint

noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint
open PrincipalCommutator ScalarBaseAdjoint

def adjointFirstCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) (i : Fin 3) : ℝ :=
  2 * (mu x)⁻¹ * ∑ j, directionalFDeriv (v j) (fun y => mu y * a y i j) x

def adjointZeroCoefficient (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) : ℝ :=
  (mu x)⁻¹ * ∑ i, ∑ j, directionalFDeriv (v j)
    (directionalFDeriv (v i) (fun y => mu y * a y i j)) x

lemma abs_sum_three_le (f : Fin 3 → ℝ) (B : ℝ) (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3*B := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum (fun i _ => h i)
    _ = 3*B := by simp

lemma adjointFirstCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) (M B : ℝ) (hM : 0 ≤ M)
    (hm : |(mu x)⁻¹| ≤ M)
    (h : ∀ i j, |directionalFDeriv (v j) (fun y => mu y*a y i j) x| ≤ B)
    (i : Fin 3) : |adjointFirstCoefficient v mu a x i| ≤ 6*M*B := by
  have hs := abs_sum_three_le _ B (h i)
  unfold adjointFirstCoefficient
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have ht := mul_le_mul hm hs (abs_nonneg _) hM
  nlinarith

lemma adjointZeroCoefficient_bound (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (x : R3) (M B : ℝ) (hM : 0 ≤ M)
    (hm : |(mu x)⁻¹| ≤ M)
    (h : ∀ i j, |directionalFDeriv (v j) (directionalFDeriv (v i)
      (fun y => mu y*a y i j)) x| ≤ B) :
    |adjointZeroCoefficient v mu a x| ≤ 9*M*B := by
  have hs := abs_sum_three_le _ (3*B) (fun i => abs_sum_three_le _ B (h i))
  unfold adjointZeroCoefficient
  rw [abs_mul]
  have ht := mul_le_mul hm hs (abs_nonneg _) hM
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scalarSecondBaseAdjoint_coefficient_form (v : Fin 3 → R3) (mu : R3 → ℝ)
    (a : MatrixField) (w : R3 → E) (hm : ContDiff ℝ ∞ mu)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun y => a y i j)) (hw : ContDiff ℝ ∞ w)
    (x : R3) (hp : mu x ≠ 0) (hs : ∀ᶠ y in 𝓝 x, (a y).IsHermitian) :
    scalarSecondBaseAdjoint v mu a w x - scalarSecondBase v a w x =
      adjointZeroCoefficient v mu a x • w x +
      ∑ i, adjointFirstCoefficient v mu a x i • directionalFDeriv (v i) w x := by
  rw [scalarSecondBaseAdjoint_sub v mu a w hm ha hw x hp hs]
  simp only [adjointZeroCoefficient,adjointFirstCoefficient,Finset.mul_sum,Finset.sum_smul,
    Finset.smul_sum,smul_smul]

end OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint
