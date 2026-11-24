module

public import Proof.CalderonPatch.DirichletHilbert
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

namespace DirichletData

variable (D : DirichletData m M)

omit [PreconnectedSpace M] in
theorem test_memLp (u : DirichletTest D) : MemLp (⇑u) 2 D.volume := sorry

omit [PreconnectedSpace M] in
/-- The function represented by a smooth test, in the metric
volume's ordinary `L²` space. -/
def testLp : DirichletTest D →ₗ[ℝ] Lp ℝ 2 D.volume where
  toFun u := (D.test_memLp u).toLp (⇑u)
  map_add' u v := by
    simpa only [DirichletTest.coe_add] using
      MemLp.toLp_add (D.test_memLp u) (D.test_memLp v)
  map_smul' r u := by
    simpa only [DirichletTest.coe_smul,RingHom.id_apply] using
      MemLp.toLp_const_smul r (D.test_memLp u)

theorem testLp_bound : ∃ C : ℝ, ∀ u : DirichletTest D, ‖D.testLp u‖ ≤ C * ‖u‖ := sorry

/-- The coercive estimate extends the value map continuously to the
zero-trace energy completion. -/
def l2Value : DirichletHilbert D →L[ℝ] Lp ℝ 2 D.volume :=
  (D.testLp.mkContinuousOfExistsBound D.testLp_bound).fromCompletion

/-- Riesz representation of the forcing functional in the exact
native gradient energy. The sign corresponds to inverting `−Δ`. -/
def weakDirichletInverse (f : Lp ℝ 2 D.volume) : DirichletHilbert D :=
  (InnerProductSpace.toDual ℝ (DirichletHilbert D)).symm
    ((innerSL ℝ f).comp D.l2Value)

theorem weakDirichletInverse_inner (f : Lp ℝ 2 D.volume) (v : DirichletHilbert D) :
    ⟪D.weakDirichletInverse f, v⟫ = ⟪f, D.l2Value v⟫ := sorry

theorem norm_weakDirichletInverse_le (f : Lp ℝ 2 D.volume) :
    ‖D.weakDirichletInverse f‖ ≤ ‖D.l2Value‖ * ‖f‖ := sorry

end DirichletData

end CalderonPatch
