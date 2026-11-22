module

public import Proof.CalderonPatch.MetricDualEnergy
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- The pointwise polarized gradient energy in the actual tangent metric. -/
def energyPairingDensity (g : SmoothMetric n M) (u v : M → ℝ) (x : M) : ℝ :=
  g.inner x (metricDual g x (mfderiv J R u x)) (metricDual g x (mfderiv J R v x))

theorem energyPairingDensity_self (g : SmoothMetric n M) (u : M → ℝ) (x : M) :
    energyPairingDensity g u u x = covectorEnergy g x (mfderiv J R u x) :=
  (covectorEnergy_eq_metricDual g x _).symm

theorem energyPairingDensity_symm (g : SmoothMetric n M) (u v : M → ℝ) (x : M) :
    energyPairingDensity g u v x = energyPairingDensity g v u x :=
  g.symm x _ _

theorem energyPairingDensity_add_left (g : SmoothMetric n M) {u v : M → ℝ}
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v) (w : M → ℝ) (x : M) :
    energyPairingDensity g (u + v) w x =
      energyPairingDensity g u w x + energyPairingDensity g v w x := by
  let a : TangentSpace J x →L[ℝ] ℝ := mfderiv J R u x
  let b : TangentSpace J x →L[ℝ] ℝ := mfderiv J R v x
  let c : TangentSpace J x →L[ℝ] ℝ := mfderiv J R w x
  let d : TangentSpace J x →L[ℝ] ℝ := mfderiv J R (u + v) x
  have hD : d = a + b :=
    mfderiv_add (hu.contMDiffAt.mdifferentiableAt (by simp)) (hv.contMDiffAt.mdifferentiableAt (by simp))
  change g.inner x (metricDual g x d) (metricDual g x c) =
    g.inner x (metricDual g x a) (metricDual g x c) + g.inner x (metricDual g x b) (metricDual g x c)
  rw [hD,metricDual_add g x a b,map_add,add_apply]

theorem energyPairingDensity_add_right (g : SmoothMetric n M) (w : M → ℝ) {u v : M → ℝ}
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v) (x : M) :
    energyPairingDensity g w (u + v) x =
      energyPairingDensity g w u x + energyPairingDensity g w v x := by
  rw [energyPairingDensity_symm g w (u + v),energyPairingDensity_add_left g hu hv w,
    energyPairingDensity_symm g u w,energyPairingDensity_symm g v w]

theorem energyPairingDensity_eq_zero_off_tsupport
    (g : SmoothMetric n M) (u v : M → ℝ) {p : M} (hp : p ∉ tsupport v) :
    energyPairingDensity g u v p = 0 := by
  have h : v =ᶠ[𝓝 p] (0 : M → ℝ) := notMem_tsupport_iff_eventuallyEq.mp hp
  have hD : (mfderiv J R v p : TangentSpace J p →L[ℝ] ℝ) = 0 := by
    have hC : (mfderiv J R (0 : M → ℝ) p : TangentSpace J p →L[ℝ] ℝ) = 0 :=
      mfderiv_const (I := J) (I' := R)
    rw [h.mfderiv_eq, hC, ContinuousLinearMap.comp_zero]
  unfold energyPairingDensity
  rw [hD]
  exact (g.symm p _ _).trans (metricDual_spec g p 0 _)

variable [MeasurableSpace M]

/-- Weak stationarity of a smooth potential tested against smooth
zero-trace variations. -/
def IsDirichletStationary (g : SmoothMetric n M) (μ : Measure M) (u : M → ℝ) : Prop :=
  ∀ w : M → ℝ, ContMDiff J R ∞ w → EqOn w 0 ((J).boundary M) →
    (∫ x, energyPairingDensity g u w x ∂μ) = 0

theorem IsDirichletStationary.add {g : SmoothMetric n M} {μ : Measure M} {u v : M → ℝ}
    (hU : IsDirichletStationary g μ u) (hV : IsDirichletStationary g μ v)
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    (hIntegrable : ∀ a b : M → ℝ, ContMDiff J R ∞ a → ContMDiff J R ∞ b →
      Integrable (energyPairingDensity g a b) μ) :
    IsDirichletStationary g μ (u + v) := by
  intro w hw hTrace
  rw [show energyPairingDensity g (u + v) w =
      (fun x => energyPairingDensity g u w x + energyPairingDensity g v w x) from
        funext (energyPairingDensity_add_left g hu hv w),
    integral_add (hIntegrable u w hu hw) (hIntegrable v w hv hw),
    hU w hw hTrace, hV w hw hTrace,add_zero]

/-- A stationary potential pairs equally with any two smooth
representatives of the same boundary trace. -/
theorem IsDirichletStationary.integral_eq_of_same_trace
    {g : SmoothMetric n M} {μ : Measure M} {u v w : M → ℝ}
    (hStationary : IsDirichletStationary g μ u)
    (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v) (hw : ContMDiff J R ∞ w)
    (hTrace : EqOn v w ((J).boundary M))
    (hIntegrable : ∀ a b : M → ℝ, ContMDiff J R ∞ a → ContMDiff J R ∞ b →
      Integrable (energyPairingDensity g a b) μ) :
    (∫ x, energyPairingDensity g u v x ∂μ) = ∫ x, energyPairingDensity g u w x ∂μ := by
  let δ := v - w
  have hδ : ContMDiff J R ∞ δ := hv.sub hw
  have hl : EqOn δ 0 ((J).boundary M) := fun x hx => sub_eq_zero.mpr (hTrace hx)
  have hEq : v = w + δ := by
    funext x
    change v x = w x + (v x - w x)
    rw [add_comm,sub_add_cancel]
  calc
    _ = ∫ x, energyPairingDensity g u (w + δ) x ∂μ := by rw [← hEq]
    _ = ∫ x, energyPairingDensity g u w x + energyPairingDensity g u δ x ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (energyPairingDensity_add_right g u hw hδ))
    _ = _ := by rw [integral_add (hIntegrable u w hu hw) (hIntegrable u δ hu hδ),
      hStationary δ hδ hl,add_zero]

/-- A smooth harmonic extension minimizes the smooth Dirichlet energy.
The stationarity hypothesis is the weak equation on smooth zero-trace
variations, with the volume and the metric of the measurement. -/
theorem dirichletQuadraticEnergy_eq_of_stationary
    (g : SmoothMetric n M) (μ : Measure M) {u f : M → ℝ}
    (hu : ContMDiff J R ∞ u) (htrace : EqOn u f ((𝓡∂ n).boundary M))
    (hIntegrable : ∀ a b : M → ℝ, ContMDiff J R ∞ a → ContMDiff J R ∞ b →
      Integrable (energyPairingDensity g a b) μ)
    (hweak : ∀ w : M → ℝ, ContMDiff J R ∞ w → EqOn w 0 ((𝓡∂ n).boundary M) →
      (∫ x, energyPairingDensity g u w x ∂μ) = 0) :
    dirichletQuadraticEnergy g μ f = ∫ x, covectorEnergy g x (mfderiv J R u x) ∂μ := by
  let E (a : M → ℝ) := ∫ x, covectorEnergy g x (mfderiv J R a x) ∂μ
  have hEint (a : M → ℝ) (ha : ContMDiff J R ∞ a) :
      Integrable (fun x => covectorEnergy g x (mfderiv J R a x)) μ := by
    have h := hIntegrable a a ha ha
    rwa [show energyPairingDensity g a a = _ from funext (energyPairingDensity_self g a)] at h
  have hMin (v : M → ℝ) (hv : ContMDiff J R ∞ v)
      (htrace' : EqOn v f ((𝓡∂ n).boundary M)) :
      E u ≤ E v := by
    let w := v - u
    have hw : ContMDiff J R ∞ w := hv.sub hu
    have hwtrace : EqOn w 0 ((𝓡∂ n).boundary M) := by
      intro x hx
      change v x - u x = 0
      rw [htrace' hx, htrace hx, sub_self]
    have hsum : v = u + w := by
      funext x
      change v x = u x + (v x - u x)
      rw [← add_sub_assoc, add_sub_cancel_left]
    have hpoint (x : M) :
        covectorEnergy g x (mfderiv J R v x) =
          covectorEnergy g x (mfderiv J R u x) + 2 * energyPairingDensity g u w x +
          covectorEnergy g x (mfderiv J R w x) := by
      have hderiv : (mfderiv J R v x : TangentSpace J x →L[ℝ] ℝ) =
          (by exact mfderiv J R u x) + (by exact mfderiv J R w x) := by
        conv_lhs => rw [hsum]
        exact mfderiv_add ((hu.contMDiffAt).mdifferentiableAt (by simp))
          ((hw.contMDiffAt).mdifferentiableAt (by simp))
      exact (congrArg (covectorEnergy g x) hderiv).trans
        (covectorEnergy_add g x (mfderiv J R u x) (mfderiv J R w x))
    have huI := hEint u hu
    have hwI := hEint w hw
    have hpairI := (hIntegrable u w hu hw).const_mul 2
    have hEnergy : E v = E u + E w := by
      calc
        _ = ∫ x, covectorEnergy g x (mfderiv J R u x) + 2 * energyPairingDensity g u w x +
            covectorEnergy g x (mfderiv J R w x) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hpoint)
        _ = (∫ x, covectorEnergy g x (mfderiv J R u x) + 2 * energyPairingDensity g u w x ∂μ) + E w :=
          integral_add (huI.add hpairI) hwI
        _ = (E u + ∫ x, 2 * energyPairingDensity g u w x ∂μ) + E w :=
          congrArg (· + E w) (integral_add huI hpairI)
        _ = _ := by rw [integral_const_mul, hweak w hw hwtrace, mul_zero, add_zero]
    have hn : 0 ≤ E w := integral_nonneg fun x => covectorEnergy_nonneg g x _
    rw [hEnergy]
    exact le_add_of_nonneg_right hn
  let A : Set ℝ := { c : ℝ | ∃ v : M → ℝ, ContMDiff J R ∞ v ∧
    EqOn v f ((𝓡∂ n).boundary M) ∧ c = E v }
  have hMem : E u ∈ A := ⟨u, hu, htrace, rfl⟩
  have hl : E u ∈ lowerBounds A := by
    rintro _ ⟨v, hv, ht, rfl⟩
    exact hMin v hv ht
  change sInf A = E u
  exact le_antisymm (csInf_le ⟨E u, hl⟩ hMem) (le_csInf ⟨E u, hMem⟩ hl)

end CalderonPatch
