module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.DilationHarmonic
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.NormalizedMetric
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem hessian_transpose {Ω : Set (X dim)} (hΩ : IsOpen Ω) {u : (X dim) → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) {x : (X dim)} (hx : x ∈ Ω) :
    (hessian u x).transpose = hessian u x := by
  have hs := (hu.contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by simp)
  have hf : DifferentiableAt ℝ (fderiv ℝ u) x := by
    have hfirst := hu.fderiv_of_isOpen hΩ (m := 1) (by simp)
    exact (hfirst.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hx)
  have he (i j : (I dim)) : hessian u x i j = fderiv ℝ (fderiv ℝ u) x (axis i) (axis j) := by
    let L : ((X dim) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (axis j)
    have h := L.hasFDerivAt.comp x hf.hasFDerivAt
    change fderiv ℝ (L ∘ fderiv ℝ u) x (axis i) = _
    rw [h.fderiv]
    rfl
  ext i j
  change hessian u x j i = hessian u x i j
  rw [he, he]
  exact hs.eq _ _

theorem trace_hessian_eq_zero {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)}
    (hchart : HarmonicCoordinates Ω g) {u : (X dim) → ℝ} (hu : Harmonic Ω g u) {x : (X dim)} (hx : x ∈ Ω) :
    ((g x)⁻¹ * hessian u x).trace = 0 := by
  have hsum := (laplace_eq_hessian_contraction hchart hx u).symm.trans (hu.2 x hx)
  calc
    _ = ((g x)⁻¹ * (hessian u x).transpose).trace := by rw [hessian_transpose hΩ hu.1 hx]
    _ = 0 := hsum

/-- The two harmonic equations and the normalization produce the pointwise
linear system for the normalized difference used in Section 6.1. -/
theorem normalized_metric_system {Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g₁ g₂ : (MetricField dim)}
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {u₁ u₂ : (X dim) → ℝ} (hu₁ : Harmonic Ω g₁ u₁) (hu₂ : Harmonic Ω g₂ u₂)
    {x : (X dim)} (hx : x ∈ Ω) (hγ : (γ x).PosDef) (hg₁ : (g₁ x).PosDef) (hg₂ : (g₂ x).PosDef)
    {c : ℝ} (hc : 0 < c) (hγ₁ : γ x = c • g₁ x) :
    ((principal γ g₂ x - (γ x)⁻¹) * hessian u₁ x).trace =
      -(principal γ g₂ x * hessian (fun y => u₂ y - u₁ y) x).trace ∧
    (γ x * (principal γ g₂ x - (γ x)⁻¹)).trace = 0 := by
  have htrace₁ := trace_hessian_eq_zero hΩ hchart₁ hu₁ hx
  have htrace₂ := trace_hessian_eq_zero hΩ hchart₂ hu₂ hx
  let a : ℝˣ := Units.mk0 c hc.ne'
  have hγinv : (γ x)⁻¹ = c⁻¹ • (g₁ x)⁻¹ := by
    rw [hγ₁]
    exact Matrix.inv_smul' _ a (isUnit_iff_ne_zero.mpr hg₁.det_pos.ne')
  have h₁ : ((γ x)⁻¹ * hessian u₁ x).trace = 0 := by
    rw [hγinv, Matrix.smul_mul, Matrix.trace_smul, htrace₁, smul_zero]
  have h₂ : (principal γ g₂ x * hessian u₂ x).trace = 0 := by
    rw [principal, Matrix.smul_mul, Matrix.trace_smul, htrace₂, smul_zero]
  refine ⟨?_, trace_normalized_difference hγ hg₂⟩
  rw [hessian_sub hΩ hu₂.1 hu₁.1 hx, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, h₁, h₂]
  linarith

/-- A symmetric matrix with zero metric trace is determined by its
contractions against any spanning family in the harmonic hyperplane. -/
theorem symmetric_eq_zero_of_spanning_traces {A H : (Mat dim)} (hA : A.PosDef)
    (hH : H.transpose = H) (hzero : (A * H).trace = 0)
    {n : ℕ} {B : Fin n → (Mat dim)}
    (hspan : ∀ V : (Mat dim), V ∈ Submodule.span ℝ (Set.range B) ↔
      V.transpose = V ∧ (A⁻¹ * V).trace = 0)
    (hvalues : ∀ a, (H * B a).trace = 0) : H = 0 := by
  let L : (Mat dim) →ₗ[ℝ] ℝ := (Matrix.traceLinearMap (I dim) ℝ ℝ).comp
    (mulLeftLinearMap (R := ℝ) (n := (I dim)) H)
  have hker : Submodule.span ℝ (Set.range B) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (hvalues a)
  have hinv : (A⁻¹ * A).trace = (dim : ℝ) := by
    rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.trace_one]
    simp [Fintype.card_fin]
  let c := (A⁻¹ * H).trace / (dim : ℝ)
  let V := H - c • A
  have hVsymm : V.transpose = V := by
    simp only [V, Matrix.transpose_sub, Matrix.transpose_smul, hH, hA.isHermitian.isSymm.eq]
  have hVtrace : (A⁻¹ * V).trace = 0 := by
    simp only [V, c, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
      hinv, smul_eq_mul]
    have hDim : (dim : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne dim
    rw [div_mul_cancel₀ _ hDim, sub_self]
  have hHV : (H * V).trace = 0 :=
    LinearMap.mem_ker.mp (hker ((hspan V).mpr ⟨hVsymm, hVtrace⟩))
  have hHA : (H * A).trace = 0 := (Matrix.trace_mul_comm _ _).trans hzero
  have hHH : (H * H).trace = 0 := by
    simpa only [V, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
      hHA, smul_zero, sub_zero] using hHV
  have hHermitian : H.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hH
  apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
  simpa only [hHermitian.eq] using hHH

end CalderonN
