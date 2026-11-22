module

public import Proof.CalderonPatch.NativePoincare
public import Mathlib.Analysis.InnerProductSpace.Completion

import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Measure.OpenPos

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

@[ext] theorem ext {u v : DirichletTest D} (h : ∀ x, u x = v x) : u = v :=
  Subtype.ext (funext h)

theorem smooth (u : DirichletTest D) : ContMDiff J R ∞ u :=
  (show ↥(smoothZeroTraceSubmodule m M) from u).property.1

theorem zero_trace (u : DirichletTest D) : EqOn u 0 ((J).boundary M) :=
  (show ↥(smoothZeroTraceSubmodule m M) from u).property.2

@[expose] def ofSmooth (u : M → ℝ) (hu : ContMDiff J R ∞ u) (hTrace : EqOn u 0 ((J).boundary M)) :
    DirichletTest D := ⟨u,by
      change ContMDiff J R ∞ u ∧ EqOn u 0 ((J).boundary M)
      exact ⟨hu,hTrace⟩⟩

@[simp] theorem ofSmooth_apply (u : M → ℝ) (hu : ContMDiff J R ∞ u)
    (hTrace : EqOn u 0 ((J).boundary M)) (x : M) :
    ofSmooth (D := D) u hu hTrace x = u x := rfl

@[simp] theorem coe_add (u v : DirichletTest D) : ⇑(u + v) = (⇑u : M → ℝ) + v := rfl

@[simp] theorem coe_smul (r : ℝ) (u : DirichletTest D) : ⇑(r • u) = r • (⇑u : M → ℝ) := rfl

@[simp] theorem zero_apply (x : M) : (0 : DirichletTest D) x = 0 := rfl

end DirichletTest

omit [MeasurableSpace M] in
theorem energyPairingDensity_const_smul_left (g : SmoothMetric N M) {u : M → ℝ}
    (hu : ContMDiff J R ∞ u) (r : ℝ) (v : M → ℝ) (x : M) :
    energyPairingDensity g (r • u) v x = r * energyPairingDensity g u v x := by
  have hD := ((hu.contMDiffAt (x := x)).mdifferentiableAt (by simp)).hasMFDerivAt.const_smul r
  let a : TangentSpace J x →L[ℝ] ℝ := mfderiv J R (r • u) x
  let b : TangentSpace J x →L[ℝ] ℝ := mfderiv J R u x
  let c : TangentSpace J x →L[ℝ] ℝ := mfderiv J R v x
  change g.inner x (metricDual g x a) (metricDual g x c) =
    r * g.inner x (metricDual g x b) (metricDual g x c)
  rw [metricDual_spec g x a,metricDual_spec g x b,show a = r • b from hD.mfderiv]
  rfl

omit [MeasurableSpace M] in
theorem energyPairingDensity_nonneg (g : SmoothMetric N M) (u : M → ℝ) (x : M) :
    0 ≤ energyPairingDensity g u u x := by
  rw [energyPairingDensity_self]
  exact covectorEnergy_nonneg g x _

variable [T2Space M] [CompactSpace M] [BorelSpace M] [PreconnectedSpace M]

namespace DirichletTest

variable (D : DirichletData m M)

theorem eq_zero_of_energy_zero (u : DirichletTest D)
    (h : ∫ x, energyPairingDensity D.metric u u x ∂D.volume = 0) : u = 0 := by
  let : IsFiniteMeasure D.volume := D.metric_volume.isFiniteMeasure
  let : D.volume.IsOpenPosMeasure :=
    ⟨fun U hU hUn => (D.metric_volume.measure_pos_of_open_nonempty hU hUn).ne'⟩
  obtain ⟨C,hP⟩ := exists_dirichlet_poincare_constant D.metric D.volume
    D.metric_volume D.boundary_nonempty
  have hU := hP u u.smooth u.zero_trace
  rw [h,mul_zero] at hU
  have hU₀ := le_antisymm hU (integral_nonneg fun x => sq_nonneg (u x))
  have hI : Integrable (fun x => (u x)^2) D.volume :=
    integrableOn_univ.mp ((u.smooth.continuous.pow 2).continuousOn.integrableOn_compact isCompact_univ)
  have hAE₂ := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (u x)) hI).mp hU₀
  have hAE : (⇑u : M → ℝ) =ᵐ[D.volume] 0 := by
    filter_upwards [hAE₂] with x hx
    change (u x)^2 = 0 at hx
    change u x = 0
    exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp hx
  have hUeq := Measure.eq_of_ae_eq hAE u.smooth.continuous continuous_const
  ext x
  exact congrFun hUeq x

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

theorem inner_eq (u v : DirichletTest D) :
    ⟪u, v⟫ = ∫ x, energyPairingDensity D.metric u v x ∂D.volume := rfl

end DirichletTest

/-- Completion of the smooth zero-trace functions in the norm
induced by their integrated Riemannian gradient pairing. -/
abbrev DirichletHilbert (D : DirichletData m M) :=
  UniformSpace.Completion (DirichletTest D)

theorem inner_dirichletHilbert_coe (D : DirichletData m M) (u v : DirichletTest D) :
    ⟪(u : DirichletHilbert D), (v : DirichletHilbert D)⟫ =
      ∫ x, energyPairingDensity D.metric u v x ∂D.volume :=
  (UniformSpace.Completion.inner_coe u v).trans (DirichletTest.inner_eq D u v)

end CalderonPatch
