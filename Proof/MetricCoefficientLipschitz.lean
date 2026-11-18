import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Matrix
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma abs_matrix_product3_sub_le (A B : Mat) (K q : ℝ) (hK : 0 ≤ K)
    (hA : ∀ i j,|A i j| ≤ K) (hB : ∀ i j,|B i j| ≤ K)
    (hDiff : ∀ i j,|A i j-B i j| ≤ q) (i j k l a b : I) :
    |A i j*A k l*A a b-B i j*B k l*B a b| ≤ 3*K^2*q := by
  have hq : 0 ≤ q := (abs_nonneg (A 0 0-B 0 0)).trans (hDiff 0 0)
  have heq : A i j*A k l*A a b-B i j*B k l*B a b =
      (A i j-B i j)*A k l*A a b+B i j*(A k l-B k l)*A a b+
        B i j*B k l*(A a b-B a b) := by ring
  have h1 : |(A i j-B i j)*A k l*A a b| ≤ q*K*K := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hDiff i j) (hA k l) (abs_nonneg _) (le_trans (abs_nonneg _) (hDiff i j)))
      (hA a b) (abs_nonneg _) (by positivity)
  have h2 : |B i j*(A k l-B k l)*A a b| ≤ K*q*K := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hB i j) (hDiff k l) (abs_nonneg _) hK)
      (hA a b) (abs_nonneg _) (by have hq := (abs_nonneg _).trans (hDiff k l); positivity)
  have h3 : |B i j*B k l*(A a b-B a b)| ≤ K*K*q := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hB i j) (hB k l) (abs_nonneg _) hK)
      (hDiff a b) (abs_nonneg _) (by positivity)
  rw [heq]
  have ht : |(A i j-B i j)*A k l*A a b+B i j*(A k l-B k l)*A a b+B i j*B k l*(A a b-B a b)| ≤
      |(A i j-B i j)*A k l*A a b|+|B i j*(A k l-B k l)*A a b|+|B i j*B k l*(A a b-B a b)| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  exact (ht.trans (add_le_add (add_le_add h1 h2) h3)).trans_eq (by ring)

/-- Dimension-three determinant Lipschitz bound on a bounded matrix-entry box. -/
lemma abs_det_sub_det_le (A B : Mat) (K q : ℝ) (hK : 0 ≤ K)
    (hA : ∀ i j,|A i j| ≤ K) (hB : ∀ i j,|B i j| ≤ K)
    (hDiff : ∀ i j,|A i j-B i j| ≤ q) : |A.det-B.det| ≤ 18*K^2*q := by
  have hTerm := abs_matrix_product3_sub_le A B K q hK hA hB hDiff
  have hAbs (a b c d e f : ℝ) : |a-b-c+d+e-f| ≤ |a|+|b|+|c|+|d|+|e|+|f| := by
    have h1 := abs_sub a b
    have h2 := abs_sub (a-b) c
    have h3 := abs_add_le (a-b-c) d
    have h4 := abs_add_le (a-b-c+d) e
    have h5 := abs_sub (a-b-c+d+e) f
    linarith only [h1,h2,h3,h4,h5]
  have heq : A.det-B.det =
      (A 0 0*A 1 1*A 2 2-B 0 0*B 1 1*B 2 2)-
      (A 0 0*A 1 2*A 2 1-B 0 0*B 1 2*B 2 1)-
      (A 0 1*A 1 0*A 2 2-B 0 1*B 1 0*B 2 2)+
      (A 0 1*A 1 2*A 2 0-B 0 1*B 1 2*B 2 0)+
      (A 0 2*A 1 0*A 2 1-B 0 2*B 1 0*B 2 1)-
      (A 0 2*A 1 1*A 2 0-B 0 2*B 1 1*B 2 0) := by rw [det_fin_three,det_fin_three]; ring
  rw [heq]
  have hh := hAbs (A 0 0*A 1 1*A 2 2-B 0 0*B 1 1*B 2 2)
    (A 0 0*A 1 2*A 2 1-B 0 0*B 1 2*B 2 1) (A 0 1*A 1 0*A 2 2-B 0 1*B 1 0*B 2 2)
    (A 0 1*A 1 2*A 2 0-B 0 1*B 1 2*B 2 0) (A 0 2*A 1 0*A 2 1-B 0 2*B 1 0*B 2 1)
    (A 0 2*A 1 1*A 2 0-B 0 2*B 1 1*B 2 0)
  linarith only [hh,hTerm 0 0 1 1 2 2,hTerm 0 0 1 2 2 1,hTerm 0 1 1 0 2 2,
    hTerm 0 1 1 2 2 0,hTerm 0 2 1 0 2 1,hTerm 0 2 1 1 2 0]

lemma abs_inverse_entry_sub_le (A B : Mat) (L q : ℝ) (hL : 0 ≤ L)
    (hAdet : A.det ≠ 0) (hBdet : B.det ≠ 0)
    (hA : ∀ i j,|A⁻¹ i j| ≤ L) (hB : ∀ i j,|B⁻¹ i j| ≤ L)
    (hDiff : ∀ i j,|A i j-B i j| ≤ q) (i j : I) :
    |A⁻¹ i j-B⁻¹ i j| ≤ 9*L^2*q := by
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hAdet)
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hBdet)
  have heq := congrArg (fun T : Mat => T i j) (Matrix.inv_sub_inv (A:=A) (B:=B) (iff_of_true hAu hBu))
  rw [Matrix.sub_apply] at heq
  rw [heq]
  change |∑ l,(∑ k,A⁻¹ i k*(B k l-A k l))*B⁻¹ l j| ≤ _
  simp only [Finset.sum_mul]
  have hTerm (k l : I) : |A⁻¹ i k*(B k l-A k l)*B⁻¹ l j| ≤ L*q*L := by
    simp only [abs_mul,abs_sub_comm (B k l) (A k l)]
    exact mul_le_mul (mul_le_mul (hA i k) (hDiff k l) (abs_nonneg _) hL)
      (hB l j) (abs_nonneg _) (by have hq := (abs_nonneg _).trans (hDiff k l); positivity)
  calc
    _ ≤ ∑ l,∑ k,|A⁻¹ i k*(B k l-A k l)*B⁻¹ l j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun l _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _l : I,∑ _k : I,L*q*L :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun k _ => hTerm k l))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- Uniform continuity estimate for the actual volume density on the elliptic class. -/
theorem Elliptic.density_difference_bound {Ω Ω' : Set X} {K : ℝ} {g h : MetricField}
    (hg : Elliptic Ω K g) (hh : Elliptic Ω' K h) (hK : 0 < K)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω') (q : ℝ)
    (hDiff : ∀ i j,|g x i j-h y i j| ≤ q) :
    |metricDensity g x-metricDensity h y| ≤ 18*K^2*metricDensityBudget K*q := by
  have hDet := abs_det_sub_det_le (g x) (h y) K q hK.le
    (fun i j => hg.entry_abs_bound hK hx i j) (fun i j => hh.entry_abs_bound hK hy i j) hDiff
  have h0g := (hg.posDef hK hx).det_pos.le
  have h0h := (hh.posDef hK hy).det_pos.le
  have hFactor : (metricDensity g x-metricDensity h y)*(metricDensity g x+metricDensity h y) =
      (g x).det-(h y).det := by
    have hgSq : (metricDensity g x)^2 = (g x).det := Real.sq_sqrt h0g
    have hhSq : (metricDensity h y)^2 = (h y).det := Real.sq_sqrt h0h
    nlinarith only [hgSq,hhSq]
  have hSum : (metricDensityBudget K)⁻¹ ≤ metricDensity g x+metricDensity h y :=
    (hg.density_bounds hK hx).1.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hAbs := congrArg abs hFactor
  rw [abs_mul,abs_of_nonneg (show 0 ≤ metricDensity g x+metricDensity h y by unfold metricDensity; positivity)] at hAbs
  have hWeighted := (mul_le_mul_of_nonneg_left hSum (abs_nonneg (metricDensity g x-metricDensity h y))).trans
    (hAbs.le.trans hDet)
  have hB : 0 < metricDensityBudget K := by unfold metricDensityBudget; positivity
  have hMult := mul_le_mul_of_nonneg_right hWeighted hB.le
  have hId : |metricDensity g x-metricDensity h y| *(metricDensityBudget K)⁻¹*metricDensityBudget K =
      |metricDensity g x-metricDensity h y| := by rw [mul_assoc,inv_mul_cancel₀ hB.ne',mul_one]
  rw [hId] at hMult
  exact hMult.trans_eq (by ring)

/-- Uniform entry Lipschitz bound for the actual divergence-form Laplace coefficient. -/
theorem Elliptic.principalCoefficient_difference_bound {Ω Ω' : Set X} {K : ℝ} {g h : MetricField}
    (hg : Elliptic Ω K g) (hh : Elliptic Ω' K h) (hK : 0 < K)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω') (q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ i j,|g x i j-h y i j| ≤ q) (i j : I) :
    |principalCoefficient g x i j-principalCoefficient h y i j| ≤
      metricDensityBudget K*(9*K^2+18*K^3)*q := by
  have hInv := abs_inverse_entry_sub_le (g x) (h y) K q hK.le
    (hg.posDef hK hx).det_pos.ne' (hh.posDef hK hy).det_pos.ne'
    (fun a b => hg.inverse_entry_bound hK hx a b) (fun a b => hh.inverse_entry_bound hK hy a b) hDiff i j
  have hDensity := hg.density_difference_bound hh hK hx hy q hDiff
  change |metricDensity g x*(g x)⁻¹ i j-metricDensity h y*(h y)⁻¹ i j| ≤ _
  have heq : metricDensity g x*(g x)⁻¹ i j-metricDensity h y*(h y)⁻¹ i j =
      metricDensity g x*((g x)⁻¹ i j-(h y)⁻¹ i j)+
        (metricDensity g x-metricDensity h y)*(h y)⁻¹ i j := by ring
  rw [heq]
  have hRho : |metricDensity g x| ≤ metricDensityBudget K :=
    by rw [abs_of_nonneg (show 0 ≤ metricDensity g x by unfold metricDensity; positivity)]; exact (hg.density_bounds hK hx).2
  have h1 : |metricDensity g x*((g x)⁻¹ i j-(h y)⁻¹ i j)| ≤ metricDensityBudget K*(9*K^2*q) := by
    rw [abs_mul]
    exact mul_le_mul hRho hInv (abs_nonneg _) (by unfold metricDensityBudget; positivity)
  have h2 : |(metricDensity g x-metricDensity h y)*(h y)⁻¹ i j| ≤ (18*K^2*metricDensityBudget K*q)*K := by
    rw [abs_mul]
    exact mul_le_mul hDensity (hh.inverse_entry_bound hK hy i j) (abs_nonneg _) (by unfold metricDensityBudget; positivity)
  exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)

end ShrinkingSpheres
