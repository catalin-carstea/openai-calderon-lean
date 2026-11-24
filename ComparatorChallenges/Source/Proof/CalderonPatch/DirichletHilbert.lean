module

public import Proof.CalderonPatch.EnergyIntegrable
public import Proof.CalderonPatch.NativeLaplace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Proof.CalderonN.LinearMetric
public import Proof.CalderonPatch.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Proof.CalderonN.Chart
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Proof.CalderonN.GreenRestriction
import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Segment
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
public import Proof.CalderonPatch.BoundaryNormalLaplacian
public import Proof.CalderonN.MetricDivergence
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Topology.Connected.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Proof.CalderonN.MetricVolumeDifferential
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Proof.CalderonPatch.DirichletMinimization

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace CalderonPatch

/-- Geometry and the measure used to construct the zero-trace
Dirichlet energy space. -/
structure DirichletData (m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
    [MeasurableSpace M] where
  metric : SmoothMetric (m + 1) M
  volume : Measure M
  metric_volume : IsMetricVolume metric volume
  boundary_nonempty : ((𝓡∂ (m + 1)).boundary M).Nonempty

/-- Smooth scalar test functions vanishing on the full native boundary. -/
def smoothZeroTraceSubmodule (m : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M] :
    Submodule ℝ (M → ℝ) where
  carrier := {u | ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ u ∧ EqOn u 0 ((𝓡∂ (m + 1)).boundary M)}
  zero_mem' := ⟨contMDiff_const,fun _ _ => rfl⟩
  add_mem' := fun {u v} hU hV => ⟨hU.1.add hV.1,by
    intro x hx
    change u x + v x = (0 : ℝ)
    simp only [hU.2 hx,hV.2 hx,Pi.zero_apply,add_zero]⟩
  smul_mem' := fun r u hU => ⟨(contMDiff_const (c := r)).mul hU.1,by
    intro x hx
    change r • u x = 0
    rw [hU.2 hx,Pi.zero_apply,smul_zero]⟩

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M]

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)

/-- Smooth zero-trace tests tagged with the geometry that defines
their norm. -/
@[expose] def DirichletTest (_ : DirichletData m M) : Type _ :=
  ↥(smoothZeroTraceSubmodule m M)

namespace DirichletTest

variable (D : DirichletData m M)

instance : AddCommGroup (DirichletTest D) :=
  inferInstanceAs (AddCommGroup ↥(smoothZeroTraceSubmodule m M))

instance : Module ℝ (DirichletTest D) :=
  inferInstanceAs (Module ℝ ↥(smoothZeroTraceSubmodule m M))

instance : CoeFun (DirichletTest D) (fun _ => M → ℝ) :=
  ⟨fun u => (u : ↥(smoothZeroTraceSubmodule m M)).val⟩

variable {D}

theorem smooth (u : DirichletTest D) : ContMDiff J R ∞ u := sorry

@[simp] theorem coe_add (u v : DirichletTest D) : ⇑(u + v) = (⇑u : M → ℝ) + v := rfl

@[simp] theorem coe_smul (r : ℝ) (u : DirichletTest D) : ⇑(r • u) = r • (⇑u : M → ℝ) := rfl

end DirichletTest

omit [MeasurableSpace M] in
theorem energyPairingDensity_const_smul_left (g : SmoothMetric N M) {u : M → ℝ}
    (hu : ContMDiff J R ∞ u) (r : ℝ) (v : M → ℝ) (x : M) :
    energyPairingDensity g (r • u) v x = r * energyPairingDensity g u v x := sorry

omit [MeasurableSpace M] in
theorem energyPairingDensity_nonneg (g : SmoothMetric N M) (u : M → ℝ) (x : M) :
    0 ≤ energyPairingDensity g u u x := sorry

variable [T2Space M] [CompactSpace M] [BorelSpace M] [PreconnectedSpace M]

namespace DirichletTest

variable (D : DirichletData m M)

theorem eq_zero_of_energy_zero (u : DirichletTest D)
    (h : ∫ x, energyPairingDensity D.metric u u x ∂D.volume = 0) : u = 0 := sorry

instance : InnerProductSpace.Core ℝ (DirichletTest D) where
  inner u v := ∫ x, energyPairingDensity D.metric u v x ∂D.volume
  conj_inner_symm u v := by
    change (∫ x, energyPairingDensity D.metric v u x ∂D.volume) =
      (∫ x, energyPairingDensity D.metric u v x ∂D.volume)
    exact integral_congr_ae (Eventually.of_forall (energyPairingDensity_symm D.metric v u))
  re_inner_nonneg u := integral_nonneg (energyPairingDensity_nonneg D.metric u)
  add_left u v w := by
    simp only [coe_add]
    simp_rw [energyPairingDensity_add_left D.metric u.smooth v.smooth w]
    exact integral_add
      (integrable_energyPairingDensity D.metric D.volume D.metric_volume u.smooth w.smooth)
      (integrable_energyPairingDensity D.metric D.volume D.metric_volume v.smooth w.smooth)
  smul_left u v r := by
    simp only [coe_smul,energyPairingDensity_const_smul_left D.metric u.smooth,
      integral_const_mul,starRingEnd_apply,star_trivial]
  definite u := eq_zero_of_energy_zero D u

instance : NormedAddCommGroup (DirichletTest D) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance : NormedSpace ℝ (DirichletTest D) :=
  InnerProductSpace.Core.toNormedSpace

instance : InnerProductSpace ℝ (DirichletTest D) := InnerProductSpace.ofCore _

end DirichletTest

/-- Completion of the smooth zero-trace functions in the norm
induced by their integrated Riemannian gradient pairing. -/
abbrev DirichletHilbert (D : DirichletData m M) :=
  UniformSpace.Completion (DirichletTest D)

end CalderonPatch
