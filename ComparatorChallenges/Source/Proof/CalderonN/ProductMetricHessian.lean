module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
public import Proof.CalderonN.StrictMetricWeight
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Module.Star
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Order.Compact
public import Mathlib.Data.Matrix.Block
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Proof.CalderonN.SphereFrame
public import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Proof.CalderonN.Coordinates
public import Proof.CalderonN.CovariantHessian

@[expose] public section

noncomputable section
open Set Matrix
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The Hessian of the defining function for the product Levi-Civita
connection of the two actual chart metrics. -/
@[expose] def productMetricHessian (g₁ g₂ : (MetricField dim)) (ρ : (X dim) × (X dim) → ℝ)
    (z v w : (X dim) × (X dim)) : ℝ :=
  fderiv ℝ (fderiv ℝ ρ) z v w -
    fderiv ℝ ρ z (connection g₁ z.1 v.1 w.1, connection g₂ z.2 v.2 w.2)

/-- Source condition at a product point, expressed using the literal
partial gradients and the product covariant Hessian. -/
@[expose] def ProductStrictHessianAt (g₁ g₂ : (MetricField dim)) (ρ : (X dim) × (X dim) → ℝ) (z : (X dim) × (X dim)) : Prop :=
  let f₁ : (X dim) → ℝ := fun x => ρ (x,z.2)
  let f₂ : (X dim) → ℝ := fun y => ρ (z.1,y)
  let a₁ : (X dim) := (covectorSq g₁ f₁ z.1)⁻¹ • chartMetricGradient g₁ f₁ z.1
  let a₂ : (X dim) := (covectorSq g₂ f₂ z.2)⁻¹ • chartMetricGradient g₂ f₂ z.2
  (fun i => coordDeriv i f₁ z.1) ≠ 0 ∧ (fun i => coordDeriv i f₂ z.2) ≠ 0 ∧
    ∀ v w : (X dim),
      metricPair g₁ z.1 (chartMetricGradient g₁ f₁ z.1) v = 0 →
      metricPair g₁ z.1 v v = metricPair g₁ z.1 a₁ a₁ →
      metricPair g₂ z.2 (chartMetricGradient g₂ f₂ z.2) w = 0 →
      metricPair g₂ z.2 w w = metricPair g₂ z.2 a₂ a₂ →
      0 < productMetricHessian g₁ g₂ ρ z (a₁,-a₂) (a₁,-a₂) +
        productMetricHessian g₁ g₂ ρ z (v,w) (v,w)

end CalderonN
