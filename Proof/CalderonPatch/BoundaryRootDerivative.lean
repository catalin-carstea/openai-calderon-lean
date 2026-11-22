module

public import Proof.CalderonPatch.BoundarySymbolRecurrence
public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix.Norms.Operator

namespace CalderonPatch

open CalderonN (I X Mat metricPair metricPair_eq_dotProduct)

variable {m : ℕ}

/-- The positive tangential characteristic root for a nonzero covector. -/
def boundaryRoot (h : Mat m) (ξ : X m) : ℝ :=
  Real.sqrt (metricPair (fun _ => h⁻¹) 0 ξ ξ)

def raisedBoundaryCovector (h : Mat m) (ξ : X m) : X m :=
  WithLp.toLp 2 (h⁻¹ *ᵥ fun i => ξ i)

theorem boundaryRoot_pos {h : Mat m} (hp : h.PosDef) {ξ : X m} (hξ : ξ ≠ 0) :
    0 < boundaryRoot h ξ :=
  Real.sqrt_pos.2 (CalderonN.metricPair_pos_of_posDef hp.inv hξ)

/-- Quadratic evaluation on a fixed covector, as a continuous linear
functional of the matrix. -/
def evaluateBoundaryQuadratic (ξ : X m) : Mat m →L[ℝ] ℝ :=
  ((∑ i : I m, ∑ j : I m,
    (ξ i * ξ j) • Matrix.entryLinearMap ℝ ℝ i j) : Mat m →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem evaluateBoundaryQuadratic_apply (ξ : X m) (A : Mat m) :
    evaluateBoundaryQuadratic ξ A = metricPair (fun _ => A) 0 ξ ξ := by
  change (∑ i : I m, ∑ j : I m,
    (ξ i * ξ j) • Matrix.entryLinearMap ℝ ℝ i j : Mat m →ₗ[ℝ] ℝ) A = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.entryLinearMap_apply, smul_eq_mul, metricPair]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem raised_eval {h : Mat m} (hp : h.PosDef) (A : Mat m) (ξ : X m) :
    evaluateBoundaryQuadratic ξ (h⁻¹ * A * h⁻¹) =
      evaluateBoundaryQuadratic (raisedBoundaryCovector h ξ) A := by
  rw [evaluateBoundaryQuadratic_apply, evaluateBoundaryQuadratic_apply,
    metricPair_eq_dotProduct, metricPair_eq_dotProduct]
  have hs : (h⁻¹).transpose = h⁻¹ := hp.inv.isHermitian.isSymm
  change (fun i => ξ i) ⬝ᵥ ((h⁻¹ * A * h⁻¹) *ᵥ fun i => ξ i) =
    (h⁻¹ *ᵥ fun i => ξ i) ⬝ᵥ (A *ᵥ (h⁻¹ *ᵥ fun i => ξ i))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hs]

/-- The actual derivative of the principal root in the normal variable. -/
theorem hasDerivAt_boundaryRoot {H : ℝ → Mat m} {s : ℝ} {A : Mat m}
    (hh : HasDerivAt H A s) (hp : (H s).PosDef) {ξ : X m} (hξ : ξ ≠ 0) :
    HasDerivAt (fun t => boundaryRoot (H t) ξ)
      (-metricPair (fun _ => A) 0 (raisedBoundaryCovector (H s) ξ) (raisedBoundaryCovector (H s) ξ) /
        (2 * boundaryRoot (H s) ξ)) s := by
  have hInv := (CalderonN.hasFDerivAt_inverseMatrix_of_isUnit (H s) hp.isUnit).comp_hasDerivAt s hh
  have hQuad := (evaluateBoundaryQuadratic ξ).hasFDerivAt.comp_hasDerivAt s hInv
  have hValue : 0 < evaluateBoundaryQuadratic ξ ((H s)⁻¹) := by
    rw [evaluateBoundaryQuadratic_apply]
    exact CalderonN.metricPair_pos_of_posDef hp.inv hξ
  have hd : HasDerivAt (fun t => evaluateBoundaryQuadratic ξ ((H t)⁻¹))
      (evaluateBoundaryQuadratic ξ (CalderonN.inverseMatrixDerivative (H s) A)) s := hQuad
  have h := hd.sqrt hValue.ne'
  change HasDerivAt (fun t => Real.sqrt (evaluateBoundaryQuadratic ξ ((H t)⁻¹))) _ s at h
  simpa only [CalderonN.inverseMatrixDerivative_apply, map_neg, raised_eval hp,
    evaluateBoundaryQuadratic_apply, boundaryRoot] using h

/-- Half the logarithmic derivative of the tangential determinant in
normal coordinates. -/
def boundaryNormalDrift (h A : Mat m) : ℝ := (h⁻¹ * A).trace / 2

/-- The linear dependence of the degree zero symbol on the first
normal jet, for an arbitrary nonzero covector. -/
def boundaryFirstNormalSymbol (h A : Mat m) (ξ : X m) : ℝ :=
  ((h⁻¹ * A).trace -
    metricPair (fun _ => A) 0 (raisedBoundaryCovector h ξ) (raisedBoundaryCovector h ξ) /
      boundaryRoot h ξ ^ 2) / 4

/-- Solving the degree one equation yields the prescribed first
normal term and the remainder from tangential symbol composition. -/
theorem boundary_degreeOne_symbol_split {h : ℝ → Mat m} {s : ℝ} {A : Mat m}
    (hh : HasDerivAt h A s) (hp : (h s).PosDef) {ξ : X m} (hξ : ξ ≠ 0)
    {b₀ tangential : ℝ}
    (hEquation : 2 * boundaryRoot (h s) ξ * b₀ =
      boundaryNormalDrift (h s) A * boundaryRoot (h s) ξ +
        deriv (fun t => boundaryRoot (h t) ξ) s + tangential) :
    b₀ = boundaryFirstNormalSymbol (h s) A ξ + tangential / (2 * boundaryRoot (h s) ξ) := by
  have hρ := (boundaryRoot_pos hp hξ).ne'
  rw [(hasDerivAt_boundaryRoot hh hp hξ).deriv] at hEquation
  rw [boundaryFirstNormalSymbol]
  apply (mul_left_cancel₀ (mul_ne_zero two_ne_zero hρ))
  rw [hEquation, boundaryNormalDrift]
  field_simp
  ring

end CalderonPatch
