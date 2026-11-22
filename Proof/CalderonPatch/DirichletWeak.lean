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
theorem test_memLp (u : DirichletTest D) : MemLp (⇑u) 2 D.volume := by
  let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
  exact u.smooth.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

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

omit [PreconnectedSpace M] in
theorem testLp_ae_eq (u : DirichletTest D) : (D.testLp u : M → ℝ) =ᵐ[D.volume] u :=
  (D.test_memLp u).coeFn_toLp

omit [PreconnectedSpace M] in
theorem norm_testLp_sq (u : DirichletTest D) :
    ‖D.testLp u‖^2 = ∫ x, (u x)^2 ∂D.volume := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.testLp_ae_eq u] with x hx
  rw [hx]
  change u x * u x = (u x)^2
  exact (pow_two _).symm

theorem testLp_bound : ∃ C : ℝ, ∀ u : DirichletTest D, ‖D.testLp u‖ ≤ C * ‖u‖ := by
  obtain ⟨B,hB⟩ := exists_dirichlet_poincare_constant D.metric D.volume
    D.metric_volume D.boundary_nonempty
  refine ⟨Real.sqrt (max B 0),fun u => ?_⟩
  have h := hB u u.smooth u.zero_trace
  rw [← DirichletTest.inner_eq D,real_inner_self_eq_norm_sq,← D.norm_testLp_sq] at h
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [← pow_two,← pow_two,mul_pow,Real.sq_sqrt (le_max_right _ _)]
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-- The coercive estimate extends the value map continuously to the
zero-trace energy completion. -/
def l2Value : DirichletHilbert D →L[ℝ] Lp ℝ 2 D.volume :=
  (D.testLp.mkContinuousOfExistsBound D.testLp_bound).fromCompletion

@[simp] theorem l2Value_coe (u : DirichletTest D) :
    D.l2Value (u : DirichletHilbert D) = D.testLp u := by
  unfold l2Value
  rw [ContinuousLinearMap.fromCompletion_apply_coe, LinearMap.mkContinuousOfExistsBound_apply]

theorem l2Value_coe_ae_eq (u : DirichletTest D) :
    (D.l2Value (u : DirichletHilbert D) : M → ℝ) =ᵐ[D.volume] u := by
  rw [l2Value_coe]
  exact D.testLp_ae_eq u

/-- Riesz representation of the forcing functional in the exact
native gradient energy. The sign corresponds to inverting `−Δ`. -/
def weakDirichletInverse (f : Lp ℝ 2 D.volume) : DirichletHilbert D :=
  (InnerProductSpace.toDual ℝ (DirichletHilbert D)).symm
    ((innerSL ℝ f).comp D.l2Value)

theorem weakDirichletInverse_inner (f : Lp ℝ 2 D.volume) (v : DirichletHilbert D) :
    ⟪D.weakDirichletInverse f, v⟫ = ⟪f, D.l2Value v⟫ :=
  InnerProductSpace.toDual_symm_apply

theorem weakDirichletInverse_on_test (f : Lp ℝ 2 D.volume) (v : DirichletTest D) :
    ⟪D.weakDirichletInverse f, (v : DirichletHilbert D)⟫ = ∫ x, f x * v x ∂D.volume := by
  rw [D.weakDirichletInverse_inner,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.l2Value_coe_ae_eq v] with x hx
  rw [hx]
  change v x * f x = f x * v x
  exact mul_comm _ _

theorem weakDirichletInverse_unique {f : Lp ℝ 2 D.volume} {u : DirichletHilbert D}
    (h : ∀ v : DirichletTest D, ⟪u, (v : DirichletHilbert D)⟫ = ∫ x, f x * v x ∂D.volume) :
    u = D.weakDirichletInverse f := by
  refine ext_inner_right ℝ fun w => ?_
  refine UniformSpace.Completion.induction_on w
    (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id))
    (fun v => (h v).trans (D.weakDirichletInverse_on_test f v).symm)

theorem norm_weakDirichletInverse_le (f : Lp ℝ 2 D.volume) :
    ‖D.weakDirichletInverse f‖ ≤ ‖D.l2Value‖ * ‖f‖ := by
  let u := D.weakDirichletInverse f
  have h : ‖u‖^2 ≤ ‖f‖ * (‖D.l2Value‖ * ‖u‖) := by
    rw [← real_inner_self_eq_norm_sq, D.weakDirichletInverse_inner]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (D.l2Value.le_opNorm u) (norm_nonneg f))
  rcases (norm_nonneg u).eq_or_lt with h₀ | hpos
  · change ‖u‖ ≤ _
    rw [← h₀]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · change ‖u‖ ≤ _
    apply le_of_mul_le_mul_right _ hpos
    calc
      ‖u‖ * ‖u‖ = ‖u‖^2 := (pow_two _).symm
      _ ≤ ‖f‖ * (‖D.l2Value‖ * ‖u‖) := h
      _ = _ := by ring

end DirichletData

end CalderonPatch
