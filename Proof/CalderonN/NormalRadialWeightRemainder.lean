module

public import Proof.CalderonN.NormalizedCoefficientRemainderC2

import Mathlib.Analysis.Matrix.Normed

import Mathlib.Tactic

/-! A smooth extension of the physical radial conormal weight with the
correct affine term and controlled first bulk jets. -/

public section

noncomputable section
open Set Filter Matrix Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN


variable {dim : ℕ} [NeZero dim]

@[expose] def scalarQuadraticCoefficient (A : X dim → Mat dim) (z : X dim) : ℝ :=
  ∑ i, ∑ j, z i*A z i j*z j

theorem contDiff_scalarQuadraticCoefficient {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (scalarQuadraticCoefficient A) := by
  unfold scalarQuadraticCoefficient
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul (contDiff_pi.mp (contDiff_pi.mp hA i) j)).mul
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff

theorem abs_scalarQuadraticCoefficient_le {A : X dim → Mat dim} {z : X dim}
    (hz : ‖z‖ ≤ 1) (q : ℝ) (hq : 0 ≤ q) (h : ‖A z‖ ≤ q) :
    |scalarQuadraticCoefficient A z| ≤ (dim : ℝ)^2*q := by
  have hz' (i : Fin dim) : |z i| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le z i).trans hz
  have hA (i j : Fin dim) : |A z i j| ≤ q := by
    rw [← Real.norm_eq_abs]
    exact (Matrix.norm_entry_le_entrywise_sup_norm (A z)).trans h
  unfold scalarQuadraticCoefficient
  calc
    _ ≤ ∑ i : Fin dim, ∑ j : Fin dim, |z i*A z i j*z j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin dim, ∑ _j : Fin dim, q := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_mul]
      exact (mul_le_mul (mul_le_mul (hz' i) (hA i j) (abs_nonneg _) zero_le_one) (hz' j)
        (abs_nonneg _) (by positivity)).trans_eq (by ring)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem norm_fderiv_scalarQuadraticCoefficient_le {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {z : X dim} (hz : ‖z‖ ≤ 1) (q : ℝ) (hq : 0 ≤ q) (h0 : ‖A z‖ ≤ q)
    (h1 : ‖fderiv ℝ A z‖ ≤ q) :
    ‖fderiv ℝ (scalarQuadraticCoefficient A) z‖ ≤ 3*(dim : ℝ)^2*q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hz' (i : Fin dim) : |z i| ≤ 1 := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le z i).trans hz
  have hv (i : Fin dim) : |v i| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le v i
  have hA0 (i j : Fin dim) : |A z i j| ≤ q := by
    rw [← Real.norm_eq_abs]
    exact (Matrix.norm_entry_le_entrywise_sup_norm (A z)).trans h0
  have hA1 (i j : Fin dim) : |fderiv ℝ A z v i j| ≤ q*‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact (Matrix.norm_entry_le_entrywise_sup_norm (fderiv ℝ A z v)).trans
      (((fderiv ℝ A z).le_opNorm v).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg v)))
  have hD (i j : Fin dim) :
      fderiv ℝ (fun x => x i*A x i j*x j) z v =
        v i*A z i j*z j + z i*(fderiv ℝ A z v i j)*z j + z i*A z i j*v j := by
    have hi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := z)
    have hj := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := z)
    have ha := (((matrixEntryL i j).hasFDerivAt).comp z (hA.differentiable (by simp) z).hasFDerivAt)
    have h := congrArg (fun L : X dim →L[ℝ] ℝ => L v) (((hi.mul ha).mul hj).fderiv)
    simp only [Function.comp_def,matrixEntryL_apply,ContinuousLinearMap.comp_apply,
      _root_.add_apply,_root_.smul_apply,smul_eq_mul,PiLp.proj_apply,
      Pi.mul_apply] at h
    exact h.trans (by ring)
  have hC (i j : Fin dim) : DifferentiableAt ℝ (fun x => x i*A x i j*x j) z :=
    ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul (contDiff_pi.mp (contDiff_pi.mp hA i) j)).mul
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff).differentiable (by simp) z
  have hF :
      fderiv ℝ (scalarQuadraticCoefficient A) z v =
        ∑ i, ∑ j, (v i*A z i j*z j + z i*(fderiv ℝ A z v i j)*z j + z i*A z i j*v j) := by
    have h := congrArg (fun L : X dim →L[ℝ] ℝ => L v)
      (HasFDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
        HasFDerivAt.sum fun j (_ : j ∈ Finset.univ) => (hC i j).hasFDerivAt).fderiv
    have he : (∑ i : Fin dim, ∑ j : Fin dim, fun x : X dim => x i*A x i j*x j) =
        scalarQuadraticCoefficient A := by
      funext x
      simp only [Finset.sum_apply,scalarQuadraticCoefficient]
    rw [he] at h
    simpa only [_root_.sum_apply,hD] using h
  rw [hF,Real.norm_eq_abs]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  calc
    _ ≤ ∑ _i : Fin dim, ∑ _j : Fin dim, 3*(q*‖v‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hI : |v i*A z i j*z j| ≤ q*‖v‖ := by
        simp only [abs_mul]
        exact (mul_le_mul (mul_le_mul (hv i) (hA0 i j) (abs_nonneg _) (norm_nonneg v))
          (hz' j) (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have hJ : |z i*(fderiv ℝ A z v i j)*z j| ≤ q*‖v‖ := by
        simp only [abs_mul]
        exact (mul_le_mul (mul_le_mul (hz' i) (hA1 i j) (abs_nonneg _) zero_le_one)
          (hz' j) (abs_nonneg _) (by positivity)).trans_eq (by ring)
      have hK : |z i*A z i j*v j| ≤ q*‖v‖ := by
        simp only [abs_mul]
        exact (mul_le_mul (mul_le_mul (hz' i) (hA0 i j) (abs_nonneg _) zero_le_one)
          (hv j) (abs_nonneg _) (by positivity)).trans_eq (by ring)
      exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hI hJ)) hK)).trans_eq (by ring)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end CalderonN
