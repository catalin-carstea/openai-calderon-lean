module

public import Proof.CalderonN.ConformalScaledGreenDataJets
public import Proof.CalderonN.ConformalCylinderAgreement
import Proof.CalderonN.Chart
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic
import Proof.CalderonN.MetricConnection
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.NormalInverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Proof.CalderonN.ProductMetricHessian
import Proof.CalderonN.SphereFrame
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Transform
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Proof.CalderonN.DilationConnection
import Proof.CalderonN.StrictMetricWeight
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Proof.CalderonN.FrameOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Proof.CalderonN.Coordinates
import Proof.CalderonN.ConformalDepth
import Proof.CalderonN.Radius
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Proof.CalderonN.Coercivity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Proof.CalderonN.MetricDensity
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Topology.Instances.Matrix
import Proof.CalderonN.DilationHarmonic
import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.SmoothMetricFrame
import Proof.CalderonN.CylinderCutoff
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Proof.CalderonN.ChartNormalization
public import Proof.CalderonN.MovingTrace

public section

open CalderonN Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Lemma 6.1 of the pinned manuscript on the fixed normalized conformal
cylinder, for the entire paired harmonic family and the same spheres,
cutoff and continued Green data as in Sections 4 and 5. -/
theorem lemma61 (hn : 3 ≤ dim)
    {normal : I dim} {Ω W Z : Set (X dim)} (hΩ : IsOpen Ω)
    (hside : ContainsAlignedSide normal Ω W)
    {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hg₁₀ : g₁ 0 = 1) (hg₂₀ : g₂ 0 = 1)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : X dim × X dim → ℝ}
    (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {a : ℕ} {u₁ u₂ : Fin a → X dim → ℝ}
    (hu₁ : ∀ i, Harmonic Ω g₁ (u₁ i)) (hu₂ : ∀ i, Harmonic Ω g₂ (u₂ i))
    (hpair : ∀ i, EqOn (u₁ i) (u₂ i) W)
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 21 + dim ≤ p)
    {ρ R ε tb K c₀ floor ε₀ C : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (htb : 0 < tb) (hK : 0 < K) (hfloor : 1 ≤ floor) (hε₀ : ε ≤ ε₀) (hC : 0 ≤ C)
    (hdepth : ∀ y, conformalDepth normal 4 y ≤ 3 * tb → parabolicHeight normal y < 1 / 4)
    (hZ : IsCompact Z) (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hZO : Z ⊆ ball (0 : X dim) 3)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : X dim) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)
    {k : ℕ} {M : Fin (k + 1) → ℝ} {Cj : Fin 9 → ℝ}
    (hSetup : ConformalCylinderSphereSetup normal g₁ g₂ E p R ε K ρ c₀ floor M Cj)
    (hEstimate : UniformEstimate (interior (coordinateCylinder normal)) (ball (0 : X dim) 3)
      K ρ c₀ M Cj floor ε₀ C)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ δ ∈ Ioc (0 : ℝ) 1,
        let Y := interior (coordinateCylinder normal)
        let χ := cylinderCutoff normal 4 tb
        let r := shrinkingRadius R p (conformalDepth normal 4) δ
        Small Y (conformalReference (depthScale normal 4) g₁ lam) (dilatedMetric g₂ lam) r ε →
        ∀ i : Fin a,
          let v₁ := renormalizedHarmonic (u₁ i 0) (fderiv ℝ (u₁ i) 0) (u₁ i) lam
          let v₂ := renormalizedHarmonic (u₁ i 0) (fderiv ℝ (u₁ i) 0) (u₂ i) lam
          eLpNorm (fun y => χ y * (v₂ y - v₁ y) / (r y) ^ 2) 2
            (volume.restrict Y) ≤ ENNReal.ofReal D := by
  sorry

end CalderonPaper
