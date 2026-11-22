module

public import Proof.CalderonN.LinearLaplacian

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

public section

/-! LinearHessian from the checked 3D Theorem 3.1 release 55d37bfe, with arbitrary ambient dimension. -/

noncomputable section
open Set Filter Matrix
open scoped ContDiff Matrix BigOperators Topology

namespace CalderonN

variable {n : ℕ} [NeZero n]

theorem harmonicCoordinates_linearPullback {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)}
    (hg : SmoothMetric Ω g) (hc : HarmonicCoordinates Ω g) (A : (X n) ≃L[ℝ] (X n)) :
    HarmonicCoordinates (A ⁻¹' Ω) (linearPullbackMetric g A) := by
  intro i
  let L : (X n) →L[ℝ] ℝ := (EuclideanSpace.proj i : (X n) →L[ℝ] ℝ).comp A.symm.toContinuousLinearMap
  have heq : (L ∘ A) = fun x => x i := by
    funext x
    change (A.symm (A x)) i = _
    rw [A.symm_apply_apply]
  have hL : Harmonic Ω g L := by
    refine ⟨L.contDiff.contDiffOn, fun x hx => ?_⟩
    rw [laplace_eq_hessian_contraction hc hx]
    have hD (j : (I n)) : coordDeriv j L = fun _ => L (axis j) := by
      funext z
      rw [coordDeriv, ContinuousLinearMap.fderiv]
    simp only [hessian, hD, coordDeriv, fderiv_const_apply, _root_.zero_apply,
      mul_zero, Finset.sum_const_zero]
  rw [← heq]
  exact harmonic_linearPullback hΩ hg A hL

/-- The second derivative acts by the same matrix congruence as the metric. -/
theorem hessian_linear_comp {Ω : Set (X n)} (hΩ : IsOpen Ω) (A : (X n) ≃L[ℝ] (X n))
    {u : (X n) → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {y : (X n)} (hy : A y ∈ Ω) :
    hessian (u ∘ A) y = (coordinateMatrix A.toContinuousLinearMap)ᵀ * hessian u (A y) *
      coordinateMatrix A.toContinuousLinearMap := by
  let M := coordinateMatrix A.toContinuousLinearMap
  have hU : IsOpen (A ⁻¹' Ω) := hΩ.preimage A.continuous
  have hD (l : (I n)) : DifferentiableAt ℝ (coordDeriv l u) (A y) :=
    ((contDiffOn_coordDeriv hu hΩ l).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)
  ext i j
  have hfirst : coordDeriv j (u ∘ A) =ᶠ[𝓝 y]
      fun z => ∑ l : (I n), M l j * (coordDeriv l u ∘ A) z := by
    filter_upwards [hU.mem_nhds (show y ∈ A ⁻¹' Ω from hy)] with z hz
    exact coordDeriv_linear_comp A.toContinuousLinearMap
      ((hu.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hz)) j
  change coordDeriv i (coordDeriv j (u ∘ A)) y = (Mᵀ * hessian u (A y) * M) i j
  have hterm (l : (I n)) : DifferentiableAt ℝ (coordDeriv l u ∘ A) y :=
    (hD l).comp y A.toContinuousLinearMap.differentiableAt
  have hd₂ : coordDeriv i (coordDeriv j (u ∘ A)) y =
      ∑ l : (I n), M l j * ∑ k : (I n), M k i * hessian u (A y) k l := by
    unfold coordDeriv at *
    rw [hfirst.fderiv_eq, fderiv_fun_sum (fun l _ => (hterm l).const_mul _)]
    simp only [_root_.sum_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [fderiv_const_mul (hterm l)]
    exact congrArg (fun v => M l j * v)
      (coordDeriv_linear_comp A.toContinuousLinearMap (hD l) i)
  rw [hd₂, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

private def matrixCongruence (M : (Mat n)) : (Mat n) →ₗ[ℝ] (Mat n) where
  toFun H := Mᵀ * H * M
  map_add' H K := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c H := by simp

private theorem matrixCongruence_comp_inverse {M B : (Mat n)} (h₂ : M * B = 1) (H : (Mat n)) :
    matrixCongruence B (matrixCongruence M H) = H := by
  have ht : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  change Bᵀ * (Mᵀ * H * M) * B = H
  calc
    _ = (Bᵀ * Mᵀ) * H * (M * B) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ht, h₂, one_mul, mul_one]

/-- The spanning condition remains exactly the inverse-trace-free symmetric
hyperplane after any invertible linear change of the common chart. -/
theorem hessianSpanning_linearPullback {Ω : Set (X n)} (hΩ : IsOpen Ω) (h₀ : (0 : (X n)) ∈ Ω)
    {m : ℕ} {g : (MetricField n)} {u : Fin m → (X n) → ℝ} (hu : ∀ a, ContDiffOn ℝ ∞ (u a) Ω)
    (hs : HessianSpanning g u) (A : (X n) ≃L[ℝ] (X n)) :
    HessianSpanning (linearPullbackMetric g A) (fun a => u a ∘ A) := by
  let M := coordinateMatrix A.toContinuousLinearMap
  let B := coordinateMatrix A.symm.toContinuousLinearMap
  let T := matrixCongruence M
  have hBM : B * M = 1 := coordinateMatrix_symm_mul A
  have hMB : M * B = 1 := coordinateMatrix_mul_symm A
  have hBTM : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hMB, Matrix.transpose_one]
  have hspan : Submodule.span ℝ (range fun a => hessian (u a ∘ A) 0) =
      (Submodule.span ℝ (range fun a => hessian (u a) 0)).map T := by
    rw [Submodule.map_span, ← range_comp]
    have he : (fun a => hessian (u a ∘ A) 0) = T ∘ fun a => hessian (u a) 0 := by
      funext a
      have h0 : A 0 ∈ Ω := by simpa only [map_zero] using h₀
      change hessian (u a ∘ A) 0 = Mᵀ * hessian (u a) 0 * M
      simpa only [map_zero] using hessian_linear_comp hΩ A (hu a) h0
    rw [he]
  have hsym (H : (Mat n)) : (T H).transpose = T H ↔ H.transpose = H := by
    have ht : (T H).transpose = T H.transpose := by
      change (Mᵀ * H * M)ᵀ = Mᵀ * Hᵀ * M
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [ht]
    constructor
    · intro h
      have he := congrArg (matrixCongruence B) h
      rwa [matrixCongruence_comp_inverse hMB, matrixCongruence_comp_inverse hMB] at he
    · exact congrArg T
  have htrace (H : (Mat n)) : ((linearPullbackMetric g A 0)⁻¹ * T H).trace = ((g 0)⁻¹ * H).trace := by
    rw [linearPullbackMetric_inv g A 0, A.map_zero]
    change ((B * (g 0)⁻¹ * Bᵀ) * (Mᵀ * H * M)).trace = _
    calc
      _ = (B * ((g 0)⁻¹ * H) * M).trace := by
        congr 1
        calc
          _ = B * ((g 0)⁻¹ * ((Bᵀ * Mᵀ) * (H * M))) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hBTM, one_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_cycle, hMB, one_mul]
  intro H
  change H ∈ Submodule.span ℝ (range fun a => hessian (u a ∘ A) 0) ↔
    H.transpose = H ∧ ((linearPullbackMetric g A 0)⁻¹ * H).trace = 0
  rw [hspan, Submodule.mem_map]
  constructor
  · rintro ⟨K, hK, rfl⟩
    exact ⟨(hsym K).mpr ((hs K).mp hK).1, (htrace K).trans ((hs K).mp hK).2⟩
  · intro hH
    let K := matrixCongruence B H
    have hTK : T K = H := matrixCongruence_comp_inverse hBM H
    apply Exists.intro K
    refine ⟨(hs K).mpr ⟨(hsym K).mp ?_, ?_⟩, hTK⟩
    · rw [hTK]
      exact hH.1
    · rw [← htrace K, hTK]
      exact hH.2

end CalderonN
