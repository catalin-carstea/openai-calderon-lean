import Proof.MatrixFamilyCalculus
import Proof.LocalFlowVariation

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

lemma abs_matrix_entry_contraction_le (A B : Mat) (K L : ℝ) (hK : 0 ≤ K) (_hL : 0 ≤ L)
    (hA : ∀ i j,|A i j| ≤ K) (hB : ∀ i j,|B i j| ≤ L) :
    |∑ i : I,∑ j : I,A i j*B i j| ≤ 9*K*L := by
  calc
    _ ≤ ∑ i : I,∑ j : I,|A i j*B i j| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : I,∑ _j : I,K*L := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => by
      rw [abs_mul];exact mul_le_mul (hA i j) (hB i j) (abs_nonneg _) hK))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

lemma matrixFamily_inverse_directional_bound {S : Set P} (hS : IsOpen S) (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,(G q).det ≠ 0)
    {p : P} (hp : p ∈ S) (a : P) (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hInv : ∀ i j,|(G p)⁻¹ i j| ≤ K) (hDA : ∀ i j,|fderiv ℝ (fun q => G q i j) p a| ≤ A) (i j : I) :
    |fderiv ℝ (fun q => (G q)⁻¹ i j) p a| ≤ 9*K^2*A := by
  rw [fderiv_matrixFamily_inverse_entries hS G hG hDet hp a i j,abs_neg]
  have hTerm (k l : I) : |(G p)⁻¹ i k*fderiv ℝ (fun q => G q k l) p a*(G p)⁻¹ l j| ≤ K*A*K := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hInv i k) (hDA k l) (abs_nonneg _) hK) (hInv l j) (abs_nonneg _) (by positivity)
  exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))).trans
    ((Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hTerm k l))).trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring))

lemma matrixFamily_density_directional_bound (G : P → Mat) (p a : P)
    (hG : ∀ i j,DifferentiableAt ℝ (fun q => G q i j) p) (hDet : 0 < (G p).det)
    (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hInv : ∀ i j,|(G p)⁻¹ i j| ≤ K) (hDA : ∀ i j,|fderiv ℝ (fun q => G q i j) p a| ≤ A) :
    |fderiv ℝ (matrixFamilyDensity G) p a| ≤ matrixFamilyDensity G p*(9*K*A) := by
  rw [fderiv_matrixFamily_density_entries G p a hG hDet,abs_mul,
    abs_of_nonneg (by dsimp [matrixFamilyDensity];positivity : 0 ≤ matrixFamilyDensity G p/2)]
  have hb := abs_matrix_entry_contraction_le (fun i j => (G p)⁻¹ j i)
    (fun i j => fderiv ℝ (fun q => G q i j) p a) K A hK hA (fun i j => hInv j i) hDA
  have hMu : 0 ≤ matrixFamilyDensity G p := Real.sqrt_nonneg _
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans
    (mul_le_mul_of_nonneg_right (by linarith : matrixFamilyDensity G p/2 ≤ matrixFamilyDensity G p) (by positivity))

/-- The mixed inverse jet uses only the two first directional jets and the
    mixed metric jet; pure second derivatives do not enter. -/
theorem matrixFamily_inverse_mixed_bound {S : Set P} (hS : IsOpen S) (G : P → Mat)
    (hG : ∀ i j,ContDiffOn ℝ ∞ (fun q => G q i j) S) (hDet : ∀ q ∈ S,(G q).det ≠ 0)
    {p : P} (hp : p ∈ S) (a b : P) (K A B C : ℝ)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hInv : ∀ i j,|(G p)⁻¹ i j| ≤ K)
    (hDA : ∀ i j,|fderiv ℝ (fun q => G q i j) p a| ≤ A)
    (hDB : ∀ i j,|fderiv ℝ (fun q => G q i j) p b| ≤ B)
    (hDAB : ∀ i j,|fderiv ℝ (fderiv ℝ (fun q => G q i j)) p b a| ≤ C) (i j : I) :
    |fderiv ℝ (fderiv ℝ (fun q => (G q)⁻¹ i j)) p b a| ≤ 162*K^3*A*B+9*K^2*C := by
  let F (k l : I) (q : P) := (G q)⁻¹ i k*fderiv ℝ (fun z => G z k l) q a*(G q)⁻¹ l j
  have hI (k l : I) : ContDiffOn ℝ ∞ (fun q => (G q)⁻¹ k l) S := contDiffOn_matrixFamily_inverse_entry G hG hDet k l
  have hDG (k l : I) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (fun z => G z k l) q a) S :=
    ((hG k l).fderiv_of_isOpen (m:=∞) hS (by simp)).clm_apply contDiffOn_const
  have hF (k l : I) : ContDiffOn ℝ ∞ (F k l) S := ((hI i k).mul (hDG k l)).mul (hI l j)
  have hEq : (fun q => fderiv ℝ (fun z => (G z)⁻¹ i j) q a) =ᶠ[𝓝 p] (fun q => -(∑ k : I,∑ l : I,F k l q)) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact fderiv_matrixFamily_inverse_entries hS G hG hDet hq a i j
  have hFD (k l : I) := ((hF k l).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp)
  have hSum : HasFDerivAt (fun q => ∑ k : I,∑ l : I,F k l q) (∑ k : I,∑ l : I,fderiv ℝ (F k l) p) p :=
    HasFDerivAt.fun_sum (fun k _ => HasFDerivAt.fun_sum (fun l _ => (hFD k l).hasFDerivAt))
  have hIdentity : fderiv ℝ (fderiv ℝ (fun q => (G q)⁻¹ i j)) p b a = -(∑ k : I,∑ l : I,fderiv ℝ (F k l) p b) := by
    have hNeg := hSum.neg
    change HasFDerivAt (fun q => -(∑ k : I,∑ l : I,F k l q)) _ p at hNeg
    rw [← fderiv_apply_const_of_contDiffAt (fun q => (G q)⁻¹ i j) p a b ((hI i j).contDiffAt (hS.mem_nhds hp)),
      hEq.fderiv_eq,hNeg.fderiv]
    simp only [_root_.neg_apply,_root_.sum_apply]
  have hIb (k l : I) : |fderiv ℝ (fun q => (G q)⁻¹ k l) p b| ≤ 9*K^2*B :=
    matrixFamily_inverse_directional_bound hS G hG hDet hp b K B hK hB hInv hDB k l
  have hTerm (k l : I) : |fderiv ℝ (F k l) p b| ≤ 18*K^3*A*B+K^2*C := by
    have hi := ((hI i k).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt
    have hj := ((hI l j).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt
    have hd := ((hDG k l).contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp) |>.hasFDerivAt
    have hProd := (hi.mul hd).mul hj
    have hValue := congrArg (fun L : P →L[ℝ] ℝ => L b) hProd.fderiv
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,Pi.mul_apply] at hValue
    rw [fderiv_apply_const_of_contDiffAt (fun q => G q k l) p a b ((hG k l).contDiffAt (hS.mem_nhds hp))] at hValue
    change fderiv ℝ (F k l) p b = _ at hValue
    have hExpanded : fderiv ℝ (F k l) p b =
        (fderiv ℝ (fun q => (G q)⁻¹ i k) p b*fderiv ℝ (fun q => G q k l) p a+
          (G p)⁻¹ i k*fderiv ℝ (fderiv ℝ (fun q => G q k l)) p b a)*(G p)⁻¹ l j+
        (G p)⁻¹ i k*fderiv ℝ (fun q => G q k l) p a*fderiv ℝ (fun q => (G q)⁻¹ l j) p b :=
      hValue.trans (by ring)
    rw [hExpanded,add_mul]
    have h1 : |fderiv ℝ (fun q => (G q)⁻¹ i k) p b*fderiv ℝ (fun q => G q k l) p a*(G p)⁻¹ l j| ≤ (9*K^2*B)*A*K := by
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hIb i k) (hDA k l) (abs_nonneg _) (by positivity)) (hInv l j) (abs_nonneg _) (by positivity)
    have h2 : |(G p)⁻¹ i k*fderiv ℝ (fderiv ℝ (fun q => G q k l)) p b a*(G p)⁻¹ l j| ≤ K*C*K := by
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hInv i k) (hDAB k l) (abs_nonneg _) hK) (hInv l j) (abs_nonneg _) (by positivity)
    have h3 : |(G p)⁻¹ i k*fderiv ℝ (fun q => G q k l) p a*fderiv ℝ (fun q => (G q)⁻¹ l j) p b| ≤ K*A*(9*K^2*B) := by
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul (hInv i k) (hDA k l) (abs_nonneg _) hK) (hIb l j) (abs_nonneg _) (by positivity)
    exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)).trans_eq (by ring)
  rw [hIdentity,abs_neg]
  exact ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))).trans
    ((Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hTerm k l))).trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring))

end ShrinkingSpheres
