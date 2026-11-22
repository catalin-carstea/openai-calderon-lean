module

public import Proof.CalderonPatch.CoordinateMetric
public import Proof.CalderonPatch.InteriorChartBasis
public import Proof.CalderonPatch.MetricDualEnergy
public import Proof.CalderonN.CovariantHessian
public import Proof.CalderonN.StrictMetricWeight

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Proof.CalderonN.ChartBilinear
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ProductPhaseAlgebra

@[expose] public section

noncomputable section
open Filter Matrix Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X I axis coordDeriv covectorSq covector_axis_sum metricPair chartMetricGradient
  metricPair_metricGradient metricPair_gradient_self)

variable {n : ℕ} [NeZero n] {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

/-- Evaluating a covector after a tangent-space isometry preserves its
squared dual norm. -/
theorem covectorEnergy_pullback
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N] [IsManifold J 1 N]
    (g₁ : SmoothMetric n N) (g₂ : SmoothMetric n M) (p : M) (q : N)
    (D : TangentSpace J p ≃L[ℝ] TangentSpace J q)
    (hD : ∀ v w, g₂.inner p v w = g₁.inner q (D v) (D w))
    (a : TangentSpace J q →L[ℝ] ℝ) :
    covectorEnergy g₂ p (a.comp D.toContinuousLinearMap) = covectorEnergy g₁ q a := by
  unfold covectorEnergy
  congr 1
  ext c
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨D v, by simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hD]⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := D.surjective w
    exact ⟨v, by simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hD]⟩

theorem covectorEnergy_eq_zero_iff (g : SmoothMetric n M) (p : M)
    (a : TangentSpace J p →L[ℝ] ℝ) : covectorEnergy g p a = 0 ↔ a = 0 := by
  rw [covectorEnergy_eq_metricDual]
  constructor
  · intro h
    have hd : metricDual g p a = 0 := by
      by_contra hn
      exact (ne_of_gt (g.pos p _ hn)) h
    ext v
    exact (metricDual_spec g p a v).symm.trans (by simp [hd])
  · rintro rfl
    exact metricDual_spec g p 0 (metricDual g p 0)

/-- The native metric gradient is the coordinate gradient pushed
forward by the inverse chart. -/
theorem metricDual_in_coordinates (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n))
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source)
    {x : X n} (hx : x ∈ e.target) :
    metricDual g (e.symm x) (mfderiv J R u (e.symm x)) =
      mfderiv K J e.symm x (chartMetricGradient (coordinateMetric g e) (u ∘ e.symm) x) := by
  let p := e.symm x
  let D : X n →L[ℝ] X n := mfderiv K J e.symm x
  let a : X n →L[ℝ] ℝ := mfderiv J R u p
  let γ := coordinateMetric g e
  let f : X n → ℝ := u ∘ e.symm
  let w := chartMetricGradient γ f x
  have hγ : (γ x).PosDef := (coordinateMetric_smooth g e he hes).2 x hx
  have hED : e.MDifferentiable J K :=
    ⟨he.mdifferentiableOn (by simp), hes.mdifferentiableOn (by simp)⟩
  have huD := (hu.contMDiffAt (e.open_source.mem_nhds (e.map_target hx))).mdifferentiableAt (by simp)
  have hD : fderiv ℝ f x = a.comp D := by
    have h := mfderiv_comp x huD (hED.mdifferentiableAt_symm hx)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hw : ∀ v : X n, g.inner p (D w) v = a v := by
    intro v
    obtain ⟨z, rfl⟩ := hED.symm.mfderiv_surjective hx v
    calc
      _ = metricPair γ x w z := (realizesCoordinateMetric g e x hx w z).symm
      _ = (fderiv ℝ f x) z :=
        (metricPair_metricGradient γ f x z hγ).trans (covector_axis_sum (fderiv ℝ f x) z).symm
      _ = _ := congrArg (fun L : X n →L[ℝ] ℝ => L z) hD
  exact (existsUnique_metricDual g p a).unique (metricDual_spec g p a) hw

/-- For a smooth scalar function, the intrinsic dual norm is the
quadratic form in its ordinary coordinate first derivatives. -/
theorem covectorEnergy_in_coordinates (g : SmoothMetric n M) (e : OpenPartialHomeomorph M (X n))
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source)
    {x : X n} (hx : x ∈ e.target) :
    covectorEnergy g (e.symm x) (mfderiv J R u (e.symm x)) =
      covectorSq (coordinateMetric g e) (u ∘ e.symm) x := by
  let p := e.symm x
  let a : TangentSpace J p →L[ℝ] ℝ := mfderiv J R u p
  let D : X n →L[ℝ] X n := mfderiv K J e.symm x
  let γ := coordinateMetric g e
  let w := chartMetricGradient γ (u ∘ e.symm) x
  have hw : metricDual g p a = D w := metricDual_in_coordinates g e he hes hu hx
  calc
    _ = g.inner p (metricDual g p a) (metricDual g p a) := covectorEnergy_eq_metricDual g p a
    _ = g.inner p (D w) (D w) := congrArg (fun z : X n => g.inner p z z) hw
    _ = metricPair γ x w w := (realizesCoordinateMetric g e x hx w w).symm
    _ = _ := metricPair_gradient_self _ _ _ ((coordinateMetric_smooth g e he hes).2 x hx)

/-- The native dual energy density of the differential is continuous
on any open interior set on which the function is smooth. -/
theorem continuousOn_covectorEnergy_mfderiv (g : SmoothMetric n M) {U : Set M}
    (hU : IsOpen U) (hI : U ⊆ (𝓡∂ n).interior M)
    {u : M → ℝ} (hu : ContMDiffOn J R ∞ u U) :
    ContinuousOn (fun p => covectorEnergy g p (mfderiv J R u p)) U := by
  intro p hp
  obtain ⟨e, hpe, heU, _, he, hes⟩ := exists_interiorChart p (hI hp) hU hp
  let f := u ∘ e.symm
  let γ := coordinateMetric g e
  have hf : ContDiffOn ℝ ∞ f e.target :=
    (hu.comp hes (fun _ hx => heU (e.map_target hx))).contDiffOn
  have hg := coordinateMetric_smooth g e he hes
  have hQ : ContinuousOn (covectorSq γ f) e.target := by
    apply ContDiffOn.continuousOn (𝕜 := ℝ) (n := ∞)
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ((CalderonN.contDiffOn_metric_inv_entry hg i j).mul
        (CalderonN.contDiffOn_coordDeriv hf e.open_target i)).mul
        (CalderonN.contDiffOn_coordDeriv hf e.open_target j)
  have hEq : (fun q => covectorEnergy g q (mfderiv J R u q)) =ᶠ[𝓝 p] (covectorSq γ f ∘ e) := by
    filter_upwards [e.open_source.mem_nhds hpe] with q hq
    have h := covectorEnergy_in_coordinates g e he hes (hu.mono heU) (e.map_source hq)
    rw [e.left_inv hq] at h
    exact h
  exact (((hQ.comp e.continuousOn e.mapsTo).continuousAt (e.open_source.mem_nhds hpe)).congr hEq.symm).continuousWithinAt

end CalderonPatch
