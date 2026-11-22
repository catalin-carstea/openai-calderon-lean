module

public import Proof.CalderonPatch.Energy

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set
open scoped Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

local notation "T" => TangentSpace (𝓡∂ n)

private def metricToDual (g : SmoothMetric n M) (x : M) : T x →ₗ[ℝ] Module.Dual ℝ (T x) where
  toFun w := (g.inner x w).toLinearMap
  map_add' v w := by ext u; simp
  map_smul' c w := by ext u; simp

private theorem metricToDual_injective (g : SmoothMetric n M) (x : M) :
    Function.Injective (metricToDual g x) := by
  intro u v h
  have hzero : metricToDual g x (u - v) = 0 := by rw [map_sub, h, sub_self]
  have hdiag : g.inner x (u - v) (u - v) = 0 :=
    congrArg (fun a : Module.Dual ℝ (T x) => a (u - v)) hzero
  exact sub_eq_zero.mp (by
    by_contra hne
    exact (ne_of_gt (g.pos x (u - v) hne)) hdiag)

/-- Positive definiteness realizes every covector by a unique metric-dual vector. -/
theorem existsUnique_metricDual (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) :
    ∃! w : T x, ∀ v : T x, g.inner x w v = a v := by
  have hDim : Module.finrank ℝ (T x) = Module.finrank ℝ (Module.Dual ℝ (T x)) := by
    rw [Subspace.dual_finrank_eq]
  have hInj := metricToDual_injective g x
  have hSurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hDim).mp hInj
  obtain ⟨w, hw⟩ := hSurj a.toLinearMap
  refine ⟨w, fun v => congrArg (fun d : Module.Dual ℝ (T x) => d v) hw, ?_⟩
  intro z hz
  apply hInj
  rw [hw]
  exact LinearMap.ext fun v => hz v

/-- Raising a covector by the metric. -/
def metricDual (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) : T x :=
  (existsUnique_metricDual g x a).exists.choose

theorem metricDual_spec (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) (v : T x) :
    g.inner x (metricDual g x a) v = a v :=
  (existsUnique_metricDual g x a).exists.choose_spec v

theorem metricDual_add (g : SmoothMetric n M) (x : M) (a b : T x →L[ℝ] ℝ) :
    metricDual g x (a + b) = metricDual g x a + metricDual g x b := by
  apply metricToDual_injective g x
  ext v
  change g.inner x (metricDual g x (a + b)) v = g.inner x (metricDual g x a + metricDual g x b) v
  simp only [map_add, add_apply, metricDual_spec]

theorem metric_normSq_nonneg (g : SmoothMetric n M) (x : M) (v : T x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · exact (g.pos x v h).le

/-- The variational expression for the dual norm attains its supremum
at the metric-dual vector. -/
theorem covectorEnergy_eq_metricDual (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) :
    covectorEnergy g x a = g.inner x (metricDual g x a) (metricDual g x a) := by
  let w := metricDual g x a
  have hSquare (v : T x) :
      2 * a v - g.inner x v v = g.inner x w w - g.inner x (v - w) (v - w) := by
    simp only [map_sub, sub_apply, g.symm x v w, show g.inner x w v = a v from metricDual_spec g x a v]
    ring
  have hUpper (v : T x) : 2 * a v - g.inner x v v ≤ g.inner x w w := by
    rw [hSquare]
    exact sub_le_self _ (metric_normSq_nonneg g x _)
  have hAttained : 2 * a w - g.inner x w w = g.inner x w w := by
    rw [hSquare w]
    simp
  unfold covectorEnergy
  refine le_antisymm (csSup_le ⟨_, w, rfl⟩ (by rintro _ ⟨v, rfl⟩; exact hUpper v)) ?_
  have hBdd : BddAbove (range fun v => 2 * a v - g.inner x v v) :=
    ⟨g.inner x w w, by rintro _ ⟨v, rfl⟩; exact hUpper v⟩
  exact hAttained ▸ le_csSup hBdd (mem_range_self w)

theorem covectorEnergy_nonneg (g : SmoothMetric n M) (x : M) (a : T x →L[ℝ] ℝ) :
    0 ≤ covectorEnergy g x a := by
  rw [covectorEnergy_eq_metricDual]
  exact metric_normSq_nonneg g x _

theorem covectorEnergy_add (g : SmoothMetric n M) (x : M) (a b : T x →L[ℝ] ℝ) :
    covectorEnergy g x (a + b) = covectorEnergy g x a +
      2 * g.inner x (metricDual g x a) (metricDual g x b) + covectorEnergy g x b := by
  simp only [covectorEnergy_eq_metricDual, metricDual_add, map_add, add_apply,
    g.symm x (metricDual g x b) (metricDual g x a)]
  ring

end CalderonPatch
