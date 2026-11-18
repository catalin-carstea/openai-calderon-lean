import Proof.MatrixFamilyDensityMixedBound
import Proof.DirectionalProductCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Operator
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma matrixFamily_coefficient_directional_bound {S : Set P} (hS : IsOpen S) (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,0 < (G q).det)
    {p : P} (hp : p ∈ S) (a : P) (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hInv : ∀ i j,|(G p)⁻¹ i j| ≤ K) (hDA : ∀ i j,|fderiv ℝ (fun q => G q i j) p a| ≤ A) (i j : I) :
    |fderiv ℝ (fun q => matrixFamilyCoefficient G q i j) p a| ≤ matrixFamilyDensity G p*(18*K^2*A) := by
  have hNe : ∀ q ∈ S,(G q).det ≠ 0 := fun q hq => (hDet q hq).ne'
  have hMu := contDiffOn_matrixFamily_density G hG hNe
  have hI := contDiffOn_matrixFamily_inverse_entry G hG hNe i j
  have hProd := ((hMu.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.mul
    ((hI.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hEq := congrArg (fun L : P →L[ℝ] ℝ => L a) hProd.fderiv
  change fderiv ℝ (fun q => matrixFamilyCoefficient G q i j) p a = _ at hEq
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hEq
  have hMuA := matrixFamily_density_directional_bound G p a
    (fun k l => ((hG k l).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)) (hDet p hp) K A hK hA hInv hDA
  have hIA := matrixFamily_inverse_directional_bound hS G hG hNe hp a K A hK hA hInv hDA i j
  have hMu0 : 0 ≤ matrixFamilyDensity G p := Real.sqrt_nonneg _
  rw [hEq]
  have h1 : |matrixFamilyDensity G p*fderiv ℝ (fun q => (G q)⁻¹ i j) p a| ≤ matrixFamilyDensity G p*(9*K^2*A) := by
    rw [abs_mul,abs_of_nonneg hMu0]
    exact mul_le_mul_of_nonneg_left hIA hMu0
  have h2 : |(G p)⁻¹ i j*fderiv ℝ (matrixFamilyDensity G) p a| ≤ K*(matrixFamilyDensity G p*(9*K*A)) := by
    rw [abs_mul]
    exact mul_le_mul (hInv i j) hMuA (abs_nonneg _) hK
  exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

/-- Mixed divergence coefficient derivatives preserve the separate metric
    jets: only A*B and the actual mixed jet C enter. -/
theorem matrixFamily_coefficient_mixed_bound {S : Set P} (hS : IsOpen S) (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,0 < (G q).det)
    {p : P} (hp : p ∈ S) (a b : P) (K A B C : ℝ)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hInv : ∀ i j,|(G p)⁻¹ i j| ≤ K)
    (hDA : ∀ i j,|fderiv ℝ (fun q => G q i j) p a| ≤ A)
    (hDB : ∀ i j,|fderiv ℝ (fun q => G q i j) p b| ≤ B)
    (hDAB : ∀ i j,|fderiv ℝ (fderiv ℝ (fun q => G q i j)) p b a| ≤ C) (i j : I) :
    |fderiv ℝ (fderiv ℝ (fun q => matrixFamilyCoefficient G q i j)) p b a| ≤
      matrixFamilyDensity G p*(486*K^3*A*B+18*K^2*C) := by
  have hNe : ∀ q ∈ S,(G q).det ≠ 0 := fun q hq => (hDet q hq).ne'
  have hMu := contDiffOn_matrixFamily_density G hG hNe
  have hI := contDiffOn_matrixFamily_inverse_entry G hG hNe i j
  have hMu0 : 0 ≤ matrixFamilyDensity G p := Real.sqrt_nonneg _
  have hMuA := matrixFamily_density_directional_bound G p a
    (fun k l => ((hG k l).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)) (hDet p hp) K A hK hA hInv hDA
  have hMuB := matrixFamily_density_directional_bound G p b
    (fun k l => ((hG k l).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)) (hDet p hp) K B hK hB hInv hDB
  have hMuAB := matrixFamily_density_mixed_bound hS G hG hDet hp a b K A B C hK hA hB hC hInv hDA hDB hDAB
  have hIA := matrixFamily_inverse_directional_bound hS G hG hNe hp a K A hK hA hInv hDA i j
  have hIB := matrixFamily_inverse_directional_bound hS G hG hNe hp b K B hK hB hInv hDB i j
  have hIAB := matrixFamily_inverse_mixed_bound hS G hG hNe hp a b K A B C hK hA hB hC hInv hDA hDB hDAB i j
  change |fderiv ℝ (fderiv ℝ (fun q => matrixFamilyDensity G q*(G q)⁻¹ i j)) p b a| ≤ _
  rw [second_fderiv_mul_apply (matrixFamilyDensity G) (fun q => (G q)⁻¹ i j) p a b
    (hMu.contDiffAt (hS.mem_nhds hp)) (hI.contDiffAt (hS.mem_nhds hp))]
  have h1 : |fderiv ℝ (fderiv ℝ (matrixFamilyDensity G)) p b a*(G p)⁻¹ i j| ≤
      (matrixFamilyDensity G p*(162*K^2*A*B+9*K*C))*K := by
    rw [abs_mul];exact mul_le_mul hMuAB (hInv i j) (abs_nonneg _) (by positivity)
  have h2 : |fderiv ℝ (matrixFamilyDensity G) p a*fderiv ℝ (fun q => (G q)⁻¹ i j) p b| ≤
      (matrixFamilyDensity G p*(9*K*A))*(9*K^2*B) := by
    rw [abs_mul];exact mul_le_mul hMuA hIB (abs_nonneg _) (by positivity)
  have h3 : |fderiv ℝ (matrixFamilyDensity G) p b*fderiv ℝ (fun q => (G q)⁻¹ i j) p a| ≤
      (matrixFamilyDensity G p*(9*K*B))*(9*K^2*A) := by
    rw [abs_mul];exact mul_le_mul hMuB hIA (abs_nonneg _) (by positivity)
  have h4 : |matrixFamilyDensity G p*fderiv ℝ (fderiv ℝ (fun q => (G q)⁻¹ i j)) p b a| ≤
      matrixFamilyDensity G p*(162*K^3*A*B+9*K^2*C) := by
    rw [abs_mul,abs_of_nonneg hMu0];exact mul_le_mul_of_nonneg_left hIAB hMu0
  exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) h4)).trans_eq (by ring)

end ShrinkingSpheres
