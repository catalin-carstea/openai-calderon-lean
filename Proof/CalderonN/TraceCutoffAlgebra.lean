module

public import Proof.CalderonN.Density

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! Adapted from `TraceCutoffAlgebra` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Multiplication of an angular field by a scalar on the center chart. -/
@[expose] def baseMul (χ : (X dim) → ℝ) (φ : (Field dim)) (p : (X dim) × (X dim)) : ℂ :=
  (χ p.1 : ℂ) * φ p

theorem differentiable_baseMul {χ : (X dim) → ℝ} {φ : (Field dim)}
    (hχ : Differentiable ℝ χ) (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (baseMul χ φ) :=
  (Complex.ofRealCLM.differentiable.comp (hχ.comp differentiable_fst)).mul hφ

theorem horizontal_baseMul_at (γ : (MetricField dim)) {χ : (X dim) → ℝ} {φ : (Field dim)}
    {y w : (X dim)} (hχ : DifferentiableAt ℝ χ y) (hφ : DifferentiableAt ℝ φ (y,w)) (i : (I dim)) :
    horizontal γ (baseMul χ φ) y w (axis i) =
      (χ y : ℂ) * horizontal γ φ y w (axis i) + ((coordDeriv i χ y : ℝ) : ℂ) * φ (y,w) := by
  let C := (Complex.ofRealCLM.comp ((fderiv ℝ χ y).comp (ContinuousLinearMap.fst ℝ (X dim) (X dim))))
  have hC : HasFDerivAt (fun p : (X dim) × (X dim) => (χ p.1 : ℂ)) C (y,w) :=
    Complex.ofRealCLM.hasFDerivAt.comp (y,w)
      (hχ.hasFDerivAt.comp (y,w) (ContinuousLinearMap.fst ℝ (X dim) (X dim)).hasFDerivAt)
  have h := (hC.mul hφ.hasFDerivAt).fderiv
  unfold horizontal
  rw [show fderiv ℝ (baseMul χ φ) (y,w) = _ from h]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,C,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',Complex.ofRealCLM_apply,coordDeriv]
  ring

/-- A fiberwise linear realization of the adjoint gives the product rule
for the same protected moving trace derivative. -/
theorem traceDerivative_baseMul (γ : (MetricField dim)) (A : (TraceAdjoint dim))
    (hA : ∀ i y, IsLinearMap ℂ (A i y))
    {χ : (X dim) → ℝ} {φ : (Field dim)} (hχ : Differentiable ℝ χ) (hφ : Differentiable ℝ φ) (i : (I dim)) :
    traceDerivative γ A i (baseMul χ φ) =
      baseMul χ (traceDerivative γ A i φ) + baseMul (coordDeriv i χ) φ := by
  funext p
  have hAχ := congrArg (fun f : (X dim) → ℂ => f p.2)
    ((hA i p.1).map_smul (χ p.1 : ℂ) (fun w => φ (p.1,w)))
  change adjointField A i (baseMul χ φ) p = (χ p.1 : ℂ) * adjointField A i φ p at hAχ
  simp only [traceDerivative, Pi.add_apply, horizontal_baseMul_at γ (hχ p.1) (hφ p) i, hAχ,baseMul]
  ring

private theorem traceDerivative_add (γ : (MetricField dim)) (A : (TraceAdjoint dim))
    (hA : ∀ i y, IsLinearMap ℂ (A i y)) {φ ψ : (Field dim)}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (i : (I dim)) :
    traceDerivative γ A i (φ+ψ) = traceDerivative γ A i φ + traceDerivative γ A i ψ := by
  funext p
  have hA' := congrArg (fun f : (X dim) → ℂ => f p.2)
    ((hA i p.1).map_add (fun w => φ (p.1,w)) (fun w => ψ (p.1,w)))
  change adjointField A i (φ+ψ) p = adjointField A i φ p + adjointField A i ψ p at hA'
  simp only [traceDerivative,hA',horizontal,Pi.add_apply,fderiv_add (hφ p) (hψ p),
    _root_.add_apply]
  ring

private theorem traceDerivative_sub (γ : (MetricField dim)) (A : (TraceAdjoint dim))
    (hA : ∀ i y, IsLinearMap ℂ (A i y)) {φ ψ : (Field dim)}
    (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ) (i : (I dim)) :
    traceDerivative γ A i (φ-ψ) = traceDerivative γ A i φ - traceDerivative γ A i ψ := by
  funext p
  have hA' := congrArg (fun f : (X dim) → ℂ => f p.2)
    ((hA i p.1).map_sub (fun w => φ (p.1,w)) (fun w => ψ (p.1,w)))
  change adjointField A i (φ-ψ) p = adjointField A i φ p - adjointField A i ψ p at hA'
  simp only [traceDerivative,hA',horizontal,Pi.sub_apply,fderiv_sub (hφ p) (hψ p),
    _root_.sub_apply]
  ring

/-- The actual commutator with a fixed center cutoff. Its second order
term differentiates only the scalar cutoff. -/
@[expose] def traceCutoffResidual (γ g₂ : (MetricField dim)) (r : (X dim) → ℝ) (A : (TraceAdjoint dim))
    (χ : (X dim) → ℝ) (φ : (Field dim)) (p : (X dim) × (X dim)) : ℂ :=
  (r p.1 : ℂ) * (
    (∑ i, ∑ j, (principal γ g₂ p.1 i j : ℂ) *
      (((coordDeriv i (coordDeriv j χ) p.1 : ℝ) : ℂ) * φ p +
        ((coordDeriv i χ p.1 : ℝ) : ℂ) * traceDerivative γ A j φ p +
        ((coordDeriv j χ p.1 : ℝ) : ℂ) * traceDerivative γ A i φ p -
        ∑ k, (christoffel γ p.1 k i j : ℂ) * (((coordDeriv k χ p.1 : ℝ) : ℂ) * φ p))) +
    ∑ k, (drift γ g₂ p.1 k : ℂ) * (((coordDeriv k χ p.1 : ℝ) : ℂ) * φ p))

/-- The cutoff identity is for the literal protected operator, including
all connection and drift terms. -/
theorem movingTrace_baseMul (γ g₂ : (MetricField dim)) (r : (X dim) → ℝ) (A : (TraceAdjoint dim))
    (hA : ∀ i y, IsLinearMap ℂ (A i y))
    {χ : (X dim) → ℝ} {φ : (Field dim)} (hχ : ContDiff ℝ 2 χ) (hφ : Differentiable ℝ φ)
    (hD : ∀ i, Differentiable ℝ (traceDerivative γ A i φ)) :
    movingTrace γ g₂ r A (baseMul χ φ) =
      baseMul χ (movingTrace γ g₂ r A φ) + traceCutoffResidual γ g₂ r A χ φ := by
  have hχD : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hχ₂ (j : (I dim)) : Differentiable ℝ (coordDeriv j χ) :=
    (((hχ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)).differentiable (by norm_num)
  have hFirst (j : (I dim)) := traceDerivative_baseMul γ A hA hχD hφ j
  have hSecond (i j : (I dim)) : traceDerivative γ A i (traceDerivative γ A j (baseMul χ φ)) =
      baseMul χ (traceDerivative γ A i (traceDerivative γ A j φ)) +
        baseMul (coordDeriv i χ) (traceDerivative γ A j φ) +
        (baseMul (coordDeriv j χ) (traceDerivative γ A i φ) +
          baseMul (coordDeriv i (coordDeriv j χ)) φ) := by
    rw [hFirst j,traceDerivative_add γ A hA
      (differentiable_baseMul hχD (hD j)) (differentiable_baseMul (hχ₂ j) hφ),
      traceDerivative_baseMul γ A hA hχD (hD j),traceDerivative_baseMul γ A hA (hχ₂ j) hφ]
  funext p
  simp only [movingTrace,hSecond]
  simp only [hFirst, Pi.add_apply, baseMul, movingTrace, traceCutoffResidual]
  simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring_nf
  all_goals ring

theorem movingTrace_sub (γ g₂ : (MetricField dim)) (r : (X dim) → ℝ) (A : (TraceAdjoint dim))
    (hA : ∀ i y, IsLinearMap ℂ (A i y))
    {φ ψ : (Field dim)} (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (hDφ : ∀ i, Differentiable ℝ (traceDerivative γ A i φ))
    (hDψ : ∀ i, Differentiable ℝ (traceDerivative γ A i ψ)) :
    movingTrace γ g₂ r A (φ-ψ) = movingTrace γ g₂ r A φ - movingTrace γ g₂ r A ψ := by
  have h₁ (j : (I dim)) := traceDerivative_sub γ A hA hφ hψ j
  have h₂ (i j : (I dim)) : traceDerivative γ A i (traceDerivative γ A j (φ-ψ)) =
      traceDerivative γ A i (traceDerivative γ A j φ) -
        traceDerivative γ A i (traceDerivative γ A j ψ) := by
    rw [h₁ j,traceDerivative_sub γ A hA (hDφ j) (hDψ j)]
  funext p
  simp only [movingTrace,h₂]
  simp only [h₁,Pi.sub_apply,movingTrace]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
  ring_nf

/-- The mean-zero density test has the source inhomogeneity with the
constant mode evaluated by the same moving trace operator. -/
theorem movingTrace_cutoffDensity (d : (Data dim))
    (hA : ∀ i y, IsLinearMap ℂ (d.adjoint i y)) {χ : (X dim) → ℝ} {ψ : (Field dim)}
    (hχ : ContDiff ℝ 2 χ) (hψ : Differentiable ℝ ψ)
    (hDψ : ∀ i, Differentiable ℝ (traceDerivative d.γ d.adjoint i ψ))
    (hD₁ : ∀ i, Differentiable ℝ (traceDerivative d.γ d.adjoint i (1 : (Field dim))))
    (hEq : movingTrace d.γ d.g₂ d.radius d.adjoint ψ = 0) :
    movingTrace d.γ d.g₂ d.radius d.adjoint (cutoffDensity χ ψ) =
      -baseMul χ (movingTrace d.γ d.g₂ d.radius d.adjoint (1 : (Field dim))) +
        traceCutoffResidual d.γ d.g₂ d.radius d.adjoint χ (ψ-1) := by
  have hc : cutoffDensity χ ψ = baseMul χ (ψ-1) := rfl
  have h₁ : Differentiable ℝ (1 : (Field dim)) := differentiable_const _
  have hD (i : (I dim)) : Differentiable ℝ (traceDerivative d.γ d.adjoint i (ψ-1)) := by
    rw [traceDerivative_sub d.γ d.adjoint hA hψ h₁]
    exact (hDψ i).sub (hD₁ i)
  rw [hc,movingTrace_baseMul d.γ d.g₂ d.radius d.adjoint hA hχ (hψ.sub h₁) hD,
    movingTrace_sub d.γ d.g₂ d.radius d.adjoint hA hψ h₁ hDψ hD₁,hEq,zero_sub]
  funext p
  simp [baseMul]

end CalderonN
