module

public import Proof.CalderonN.LinearMetric

import Proof.CalderonN.MetricDivergence
import Mathlib.Tactic

public section

/-! LinearLaplacian from the checked 3D Theorem 3.1 release 55d37bfe, with arbitrary ambient dimension. -/

noncomputable section
open Set Matrix Filter
open scoped ContDiff Matrix BigOperators Topology

namespace CalderonN

variable {n : ℕ} [NeZero n]

private theorem flux_as_mulVec (g : (MetricField n)) (u : (X n) → ℝ) (y : (X n)) :
    (fun i => divergenceFlux g u y i) =
      chartVolume g y • ((g y)⁻¹ *ᵥ (fun j => coordDeriv j u y)) := by
  ext i
  simp only [divergenceFlux, divergenceCoeff, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

private theorem linearPullbackFlux {u : (X n) → ℝ} {y : (X n)} (A : (X n) ≃L[ℝ] (X n))
    (hu : DifferentiableAt ℝ u (A y)) (g : (MetricField n)) (i : (I n)) :
    divergenceFlux (linearPullbackMetric g A) (u ∘ A) y i =
      |(coordinateMatrix A.toContinuousLinearMap).det| * ∑ j : (I n),
        coordinateMatrix A.symm.toContinuousLinearMap i j * divergenceFlux g u (A y) j := by
  let M := coordinateMatrix A.toContinuousLinearMap
  let B := coordinateMatrix A.symm.toContinuousLinearMap
  let F := fun j => divergenceFlux g u (A y) j
  let V := fun j => coordDeriv j u (A y)
  have hgrad : (fun j => coordDeriv j (u ∘ A) y) = Mᵀ *ᵥ V := by
    funext j
    change coordDeriv j (u ∘ A.toContinuousLinearMap) y = (Mᵀ *ᵥ V) j
    rw [coordDeriv_linear_comp A.toContinuousLinearMap hu]
    rfl
  have hBM : Bᵀ * Mᵀ = 1 := by
    rw [← Matrix.transpose_mul, coordinateMatrix_mul_symm, Matrix.transpose_one]
  have hvec : (fun j => divergenceFlux (linearPullbackMetric g A) (u ∘ A) y j) =
      |M.det| • (B *ᵥ F) := by
    rw [flux_as_mulVec, linearPullbackMetric_volume, linearPullbackMetric_inv, hgrad]
    change (|M.det| * chartVolume g (A y)) •
      ((B * (g (A y))⁻¹ * Bᵀ) *ᵥ (Mᵀ *ᵥ V)) = |M.det| • (B *ᵥ F)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (B * (g (A y))⁻¹) Bᵀ Mᵀ, hBM, mul_one,
      mul_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    rw [show F = chartVolume g (A y) • ((g (A y))⁻¹ *ᵥ V) from flux_as_mulVec g u (A y)]
  exact congrFun hvec i

/-- Covariance of the actual Laplace–Beltrami operator under a constant
linear chart change. This uses the transformation of the divergence flux. -/
theorem laplace_linearPullback {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)}
    (hg : SmoothMetric U g) (A : (X n) ≃L[ℝ] (X n)) {u : (X n) → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {y : (X n)} (hy : A y ∈ U) :
    laplace (linearPullbackMetric g A) (u ∘ A) y = laplace g u (A y) := by
  let M := coordinateMatrix A.toContinuousLinearMap
  let B := coordinateMatrix A.symm.toContinuousLinearMap
  let J := |M.det|
  let f (j : (I n)) (z : (X n)) := divergenceFlux g u z j
  let U' := A ⁻¹' U
  have hU' : IsOpen U' := hU.preimage A.continuous
  have hu' : ContDiffOn ℝ ∞ (u ∘ A) U' :=
    hu.comp A.toContinuousLinearMap.contDiff.contDiffOn (fun _ hx => hx)
  have hf (j : (I n)) : ContDiffOn ℝ ∞ (f j) U := contDiffOn_divergenceFlux hU hg hu j
  have hflux (i : (I n)) :
      (fun z => divergenceFlux (linearPullbackMetric g A) (u ∘ A) z i) =ᶠ[𝓝 y]
        fun z => ∑ j : (I n), (J * B i j) * (f j ∘ A) z := by
    filter_upwards [hU'.mem_nhds (show y ∈ U' from hy)] with z hz
    rw [linearPullbackFlux A (hu.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hz))]
    simp only [J, M, B, f, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hc (i : (I n)) : coordDeriv i (fun z => divergenceFlux (linearPullbackMetric g A) (u ∘ A) z i) y =
      ∑ j : (I n), (J * B i j) * ∑ k : (I n), M k i * coordDeriv k (f j) (A y) := by
    unfold coordDeriv
    rw [(hflux i).fderiv_eq, fderiv_fun_sum]
    · simp only [_root_.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [fderiv_const_mul]
      · exact congrArg (fun v => (J * B i j) * v)
          (coordDeriv_linear_comp A.toContinuousLinearMap
            ((hf j).differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hy)) i)
      · exact ((hf j).differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hy)).comp y
          A.toContinuousLinearMap.differentiableAt
    · intro j _
      exact (((hf j).differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds hy)).comp y
        A.toContinuousLinearMap.differentiableAt).const_mul _
  have hsum :
      (∑ i : (I n), ∑ j : (I n), (J * B i j) * ∑ k : (I n), M k i * coordDeriv k (f j) (A y)) =
        J * ∑ j : (I n), coordDeriv j (f j) (A y) := by
    have he (i j k : (I n)) : (J * B i j) * (M k i * coordDeriv k (f j) (A y)) =
        J * ((M k i * B i j) * coordDeriv k (f j) (A y)) := by ring
    simp_rw [Finset.mul_sum, he, ← Finset.mul_sum]
    congr 1
    calc
      _ = ∑ j : (I n), ∑ k : (I n), ∑ i : (I n), (M k i * B i j) * coordDeriv k (f j) (A y) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := by
        simp_rw [← Finset.sum_mul, ← Matrix.mul_apply]
        have hMB : M * B = 1 := coordinateMatrix_mul_symm A
        simp [hMB, Matrix.one_apply, ite_mul]
  have heq := chartVolume_mul_laplace_eq_divergence hU' (smoothMetric_linearPullback hg A) hu'
    (show y ∈ U' from hy)
  rw [linearPullbackMetric_volume] at heq
  simp_rw [hc] at heq
  rw [hsum, ← chartVolume_mul_laplace_eq_divergence hU hg hu hy] at heq
  have hρ : chartVolume g (A y) ≠ 0 := (Real.sqrt_pos.mpr (hg.2 (A y) hy).det_pos).ne'
  exact mul_left_cancel₀ (mul_ne_zero (abs_ne_zero.mpr (coordinateMatrix_det_ne_zero A)) hρ)
    (heq.trans (by rw [mul_assoc]))

theorem harmonic_linearPullback {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)}
    (hg : SmoothMetric U g) (A : (X n) ≃L[ℝ] (X n)) {u : (X n) → ℝ} (hu : Harmonic U g u) :
    Harmonic (A ⁻¹' U) (linearPullbackMetric g A) (u ∘ A) :=
  ⟨hu.1.comp A.toContinuousLinearMap.contDiff.contDiffOn (fun _ hx => hx),
    fun _ hx => (laplace_linearPullback hU hg A hu.1 hx).trans (hu.2 _ hx)⟩

end CalderonN
