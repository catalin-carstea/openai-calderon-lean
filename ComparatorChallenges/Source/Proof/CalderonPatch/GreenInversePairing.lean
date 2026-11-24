module

public import Proof.CalderonPatch.NativeInverseRegularity
public import Proof.CalderonPatch.NativeLaplace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Proof.CalderonN.GreenRestriction
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic
public import Proof.CalderonPatch.DirichletHilbert
public import Proof.CalderonPatch.DirichletWeak

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- Smooth scalar forcings, with no boundary condition imposed on the source. -/
@[expose] def smoothSourceSubmodule :
    Submodule ℝ (M → ℝ) where
  carrier := {q | ContMDiff J R ∞ q}
  zero_mem' := contMDiff_const
  add_mem' hq hr := hq.add hr
  smul_mem' a q hq := by
    change ContMDiff J R ∞ ((a • ContinuousLinearMap.id ℝ ℝ) ∘ q)
    exact (a • ContinuousLinearMap.id ℝ ℝ).contMDiff.comp hq

local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

instance : CoeFun Source (fun _ => M → ℝ) := ⟨Subtype.val⟩

namespace DirichletData

variable (D : DirichletData m M)

/-- The weak inverse as a bounded operator on the actual metric L². -/
@[expose] def weakInverseL2 : Lp ℝ 2 D.volume →L[ℝ] Lp ℝ 2 D.volume := by
  let F : Lp ℝ 2 D.volume →ₗ[ℝ] DirichletHilbert D :=
    { toFun := D.weakDirichletInverse
      map_add' := fun f g => by
        apply ext_inner_right ℝ
        intro v
        rw [D.weakDirichletInverse_inner, inner_add_left, inner_add_left,
          D.weakDirichletInverse_inner, D.weakDirichletInverse_inner]
      map_smul' := fun a f => by
        apply ext_inner_right ℝ
        intro v
        rw [D.weakDirichletInverse_inner, real_inner_smul_left, real_inner_smul_left,
          D.weakDirichletInverse_inner]
        rfl }
  exact D.l2Value.comp (F.mkContinuous ‖D.l2Value‖ D.norm_weakDirichletInverse_le)

omit [T2Space M] [PreconnectedSpace M] in
theorem smoothSource_memLp (p : ℝ≥0∞) (q : Source) :
    MemLp (q : M → ℝ) p D.volume := sorry

omit [PreconnectedSpace M] in
/-- Smooth native forcings as metric Lᵖ functions. -/
@[expose] def smoothSourceToLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Source →ₗ[ℝ] Lp ℝ p D.volume where
  toFun q := (D.smoothSource_memLp p q).toLp (q : M → ℝ)
  map_add' q r := MemLp.toLp_add (D.smoothSource_memLp p q) (D.smoothSource_memLp p r)
  map_smul' a q := MemLp.toLp_const_smul a (D.smoothSource_memLp p q)

omit [T2Space M] [PreconnectedSpace M] in
theorem smoothSourceToLp_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (q : Source) :
    (D.smoothSourceToLp p q : M → ℝ) =ᵐ[D.volume] (q : M → ℝ) := sorry

/-- The smooth representative of the actual bounded weak inverse
on globally smooth forcings. -/
def smoothInverse (h : NativeInverseRegularity D) (q : Source) : M → ℝ :=
  (h.smooth_solution (D.smoothSourceToLp 2 q) q (show ContMDiff J R ∞ (q : M → ℝ) from q.property) (D.smoothSourceToLp_ae 2 q)).choose

theorem smoothInverse_spec (h : NativeInverseRegularity D) (q : Source) :
    ContMDiff J R ∞ (D.smoothInverse h q) ∧
      EqOn (D.smoothInverse h q) 0 ((J).boundary M) ∧
      EqOn (-nativeLaplace D.metric (D.smoothInverse h q)) q ((J).interior M) ∧
      (D.weakInverseL2 (D.smoothSourceToLp 2 q) : M → ℝ) =ᵐ[D.volume] D.smoothInverse h q := sorry

end DirichletData

end CalderonPatch
