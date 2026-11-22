module

public import Proof.CalderonPatch.NativeInverseRegularity
public import Proof.CalderonPatch.InteriorTests

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

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

theorem weakInverseL2_apply (f : Lp ℝ 2 D.volume) :
    D.weakInverseL2 f = D.l2Value (D.weakDirichletInverse f) := rfl

/-- Reciprocity is an identity in the native energy space. -/
theorem weakInverseL2_symmetric (f g : Lp ℝ 2 D.volume) :
    ⟪D.weakInverseL2 f, g⟫ = ⟪f, D.weakInverseL2 g⟫ := by
  simp only [D.weakInverseL2_apply]
  rw [real_inner_comm, ← D.weakDirichletInverse_inner, ← D.weakDirichletInverse_inner,
    real_inner_comm]

theorem weakInverseL2_positiveLaplaceLp (v : DirichletTest D) :
    D.weakInverseL2 (D.positiveLaplaceLp v v.smooth) = D.testLp v := by
  rw [weakInverseL2_apply, ← D.l2Value_coe]
  congr 1
  symm
  apply D.weakDirichletInverse_unique
  intro z
  rw [real_inner_comm, D.inner_dirichletHilbert_test_eq_laplace, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.l2Value_coe_ae_eq z] with x hx
  rw [hx]
  simp

omit [CompactSpace M] [T2Space M] [PreconnectedSpace M] in
theorem eqOn_open_of_ae_eq {U : Set M} (hU : IsOpen U) {u v : M → ℝ}
    (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (he : u =ᵐ[D.volume.restrict U] v) : EqOn u v U := by
  let : D.volume.IsOpenPosMeasure := ⟨fun W hW hne =>
    (D.metric_volume.measure_pos_of_open_nonempty hW hne).ne'⟩
  exact Measure.eqOn_open_of_ae_eq he hU hu hv

omit [T2Space M] [PreconnectedSpace M] in
theorem smoothSource_memLp (p : ℝ≥0∞) (q : Source) :
    MemLp (q : M → ℝ) p D.volume := by
  let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
  exact q.property.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [PreconnectedSpace M] in
/-- Smooth native forcings as metric Lᵖ functions. -/
@[expose] def smoothSourceToLp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Source →ₗ[ℝ] Lp ℝ p D.volume where
  toFun q := (D.smoothSource_memLp p q).toLp (q : M → ℝ)
  map_add' q r := MemLp.toLp_add (D.smoothSource_memLp p q) (D.smoothSource_memLp p r)
  map_smul' a q := MemLp.toLp_const_smul a (D.smoothSource_memLp p q)

omit [T2Space M] [PreconnectedSpace M] in
theorem smoothSourceToLp_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (q : Source) :
    (D.smoothSourceToLp p q : M → ℝ) =ᵐ[D.volume] (q : M → ℝ) :=
  (D.smoothSource_memLp p q).coeFn_toLp

omit [T2Space M] [PreconnectedSpace M] in
theorem norm_smoothSourceToLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (q : Source) :
    ‖D.smoothSourceToLp p q‖ = (eLpNorm (q : M → ℝ) p D.volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (D.smoothSourceToLp_ae p q)]

/-- The smooth representative of the actual bounded weak inverse
on globally smooth forcings. -/
def smoothInverse (h : NativeInverseRegularity D) (q : Source) : M → ℝ :=
  (h.smooth_solution (D.smoothSourceToLp 2 q) q (show ContMDiff J R ∞ (q : M → ℝ) from q.property) (D.smoothSourceToLp_ae 2 q)).choose

theorem smoothInverse_spec (h : NativeInverseRegularity D) (q : Source) :
    ContMDiff J R ∞ (D.smoothInverse h q) ∧
      EqOn (D.smoothInverse h q) 0 ((J).boundary M) ∧
      EqOn (-nativeLaplace D.metric (D.smoothInverse h q)) q ((J).interior M) ∧
      (D.weakInverseL2 (D.smoothSourceToLp 2 q) : M → ℝ) =ᵐ[D.volume] D.smoothInverse h q := by
  rw [D.weakInverseL2_apply]
  exact (h.smooth_solution (D.smoothSourceToLp 2 q) q (show ContMDiff J R ∞ (q : M → ℝ) from q.property)
    (D.smoothSourceToLp_ae 2 q)).choose_spec

theorem smoothInverse_unique (h : NativeInverseRegularity D) (q : Source)
    {u : M → ℝ} (hu : ContMDiff J R ∞ u)
    (hAE : (D.weakInverseL2 (D.smoothSourceToLp 2 q) : M → ℝ) =ᵐ[D.volume] u) :
    D.smoothInverse h q = u := by
  apply (Set.eqOn_univ _ _).mp
  exact D.eqOn_open_of_ae_eq isOpen_univ (D.smoothInverse_spec h q).1.continuous.continuousOn
    hu.continuous.continuousOn (by
      rw [Measure.restrict_univ]
      exact (D.smoothInverse_spec h q).2.2.2.symm.trans hAE)

@[expose] def smoothInverseL (h : NativeInverseRegularity D) : Source →ₗ[ℝ] (M → ℝ) where
  toFun := D.smoothInverse h
  map_add' q r := by
    apply D.smoothInverse_unique h (q + r)
      ((D.smoothInverse_spec h q).1.add (D.smoothInverse_spec h r).1)
    rw [map_add, map_add]
    exact (Lp.coeFn_add _ _).trans
      ((D.smoothInverse_spec h q).2.2.2.add (D.smoothInverse_spec h r).2.2.2)
  map_smul' a q := by
    have hu : ContMDiff J R ∞ (a • D.smoothInverse h q) := by
      change ContMDiff J R ∞ ((a • ContinuousLinearMap.id ℝ ℝ) ∘ D.smoothInverse h q)
      exact (a • ContinuousLinearMap.id ℝ ℝ).contMDiff.comp (D.smoothInverse_spec h q).1
    apply D.smoothInverse_unique h (a • q) hu
    rw [map_smul, map_smul]
    exact (Lp.coeFn_smul _ _).trans ((D.smoothInverse_spec h q).2.2.2.const_smul a)

theorem smoothInverseL_apply (h : NativeInverseRegularity D) (q : Source) :
    D.smoothInverseL h q = D.smoothInverse h q := rfl

end DirichletData

end CalderonPatch
