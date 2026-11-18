import Proof.MatrixFamilyDirectionalBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Operator
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A mixed density jet uses only the two first directional metric jets and
    their mixed jet. No pure second metric derivative budget is needed. -/
theorem matrixFamily_density_mixed_bound {S : Set P} (hS : IsOpen S) (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,0 < (G q).det)
    {p : P} (hp : p ∈ S) (a b : P) (K A B C : ℝ)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hInv : ∀ i j,|(G p)⁻¹ i j| ≤ K)
    (hDA : ∀ i j,|fderiv ℝ (fun q => G q i j) p a| ≤ A)
    (hDB : ∀ i j,|fderiv ℝ (fun q => G q i j) p b| ≤ B)
    (hDAB : ∀ i j,|fderiv ℝ (fderiv ℝ (fun q => G q i j)) p b a| ≤ C) :
    |fderiv ℝ (fderiv ℝ (matrixFamilyDensity G)) p b a| ≤
      matrixFamilyDensity G p*(162*K^2*A*B+9*K*C) := by
  let T : P → ℝ := fun q => ∑ i : I,∑ j : I,(G q)⁻¹ j i*fderiv ℝ (fun z => G z i j) q a
  have hNe : ∀ q ∈ S,(G q).det ≠ 0 := fun q hq => (hDet q hq).ne'
  have hI (i j : I) := contDiffOn_matrixFamily_inverse_entry G hG hNe i j
  have hDG (i j : I) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (fun z => G z i j) q a) S :=
    ((hG i j).fderiv_of_isOpen (m:=∞) hS (by simp)).clm_apply contDiffOn_const
  have hMu := contDiffOn_matrixFamily_density G hG hNe
  have hT : ContDiffOn ℝ ∞ T S := ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hI j i).mul (hDG i j)))
  have hTValue : |T p| ≤ 9*K*A := abs_matrix_entry_contraction_le
    (fun i j => (G p)⁻¹ j i) (fun i j => fderiv ℝ (fun q => G q i j) p a)
    K A hK hA (fun i j => hInv j i) hDA
  have hIb (i j : I) : |fderiv ℝ (fun q => (G q)⁻¹ i j) p b| ≤ 9*K^2*B :=
    matrixFamily_inverse_directional_bound hS G hG hNe hp b K B hK hB hInv hDB i j
  have hDT : |fderiv ℝ T p b| ≤ 81*K^2*A*B+9*K*C := by
    have hTerm (i j : I) : |fderiv ℝ (fun q => (G q)⁻¹ j i*fderiv ℝ (fun z => G z i j) q a) p b| ≤
        (9*K^2*B)*A+K*C := by
      have hProd := (((hI j i).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.mul
        (((hDG i j).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      have hValue := congrArg (fun L : P →L[ℝ] ℝ => L b) hProd.fderiv
      simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hValue
      rw [fderiv_apply_const_of_contDiffAt (fun q => G q i j) p a b ((hG i j).contDiffAt (hS.mem_nhds hp))] at hValue
      change fderiv ℝ (fun q => (G q)⁻¹ j i*fderiv ℝ (fun z => G z i j) q a) p b = _ at hValue
      rw [hValue]
      have h1 : |(G p)⁻¹ j i*fderiv ℝ (fderiv ℝ (fun q => G q i j)) p b a| ≤ K*C := by
        rw [abs_mul];exact mul_le_mul (hInv j i) (hDAB i j) (abs_nonneg _) hK
      have h2 : |fderiv ℝ (fun q => G q i j) p a*fderiv ℝ (fun q => (G q)⁻¹ j i) p b| ≤ A*(9*K^2*B) := by
        rw [abs_mul];exact mul_le_mul (hDA i j) (hIb j i) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
    have hSum : HasFDerivAt T
        (∑ i : I,∑ j : I,fderiv ℝ (fun q => (G q)⁻¹ j i*fderiv ℝ (fun z => G z i j) q a) p) p :=
      HasFDerivAt.fun_sum (fun i _ => HasFDerivAt.fun_sum (fun j _ =>
        (((hI j i).mul (hDG i j)).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt))
    rw [hSum.fderiv]
    simp only [_root_.sum_apply]
    exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))).trans
      ((Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))).trans_eq (by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring))
  have hEq : (fun q => fderiv ℝ (matrixFamilyDensity G) q a) =ᶠ[𝓝 p]
      (fun q => (1/2:ℝ)*(matrixFamilyDensity G q*T q)) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    rw [fderiv_matrixFamily_density_entries G q a
      (fun i j => ((hG i j).contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp)) (hDet q hq)]
    dsimp only [T]
    ring
  have hProduct := ((((hMu.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.mul
    ((hT.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt).const_smul (1/2:ℝ))
  change HasFDerivAt (fun q => (1/2:ℝ)*(matrixFamilyDensity G q*T q)) _ p at hProduct
  have hIdentity : fderiv ℝ (fderiv ℝ (matrixFamilyDensity G)) p b a =
      (1/2:ℝ)*(fderiv ℝ (matrixFamilyDensity G) p b*T p+matrixFamilyDensity G p*fderiv ℝ T p b) := by
    rw [← fderiv_apply_const_of_contDiffAt (matrixFamilyDensity G) p a b (hMu.contDiffAt (hS.mem_nhds hp)),
      hEq.fderiv_eq,hProduct.fderiv]
    simp only [_root_.smul_apply,_root_.add_apply,smul_eq_mul]
    ring
  have hMuB := matrixFamily_density_directional_bound G p b
    (fun i j => ((hG i j).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)) (hDet p hp)
    K B hK hB hInv hDB
  have hMu0 : 0 ≤ matrixFamilyDensity G p := Real.sqrt_nonneg _
  have h1 : |fderiv ℝ (matrixFamilyDensity G) p b*T p| ≤ matrixFamilyDensity G p*(9*K*B)*(9*K*A) := by
    rw [abs_mul]
    exact mul_le_mul hMuB hTValue (abs_nonneg _) (by positivity)
  have h2 : |matrixFamilyDensity G p*fderiv ℝ T p b| ≤ matrixFamilyDensity G p*(81*K^2*A*B+9*K*C) := by
    rw [abs_mul,abs_of_nonneg hMu0]
    exact mul_le_mul_of_nonneg_left hDT hMu0
  rw [hIdentity,abs_mul]
  exact (mul_le_mul (show |(1/2:ℝ)| ≤ 1 by norm_num)
    ((abs_add_le _ _).trans (add_le_add h1 h2)) (abs_nonneg _) zero_le_one).trans_eq (by ring)

end ShrinkingSpheres
