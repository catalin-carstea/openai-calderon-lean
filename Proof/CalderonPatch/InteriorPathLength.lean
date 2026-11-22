module

public import Proof.CalderonPatch.MatchedCoordinates
public import Mathlib.Geometry.Manifold.Riemannian.Basic

@[expose] public section

noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- The length integral of an ambient curve over its parameter interval,
expressed in the specified smooth tangent metric. -/
def nativePathLength (g : SmoothMetric n M₂) (γ : ℝ → M₂) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a b, ENNReal.ofReal (Real.sqrt (g.inner (γ t)
    (mfderiv R J γ t 1) (mfderiv R J γ t 1)))

/-- The length integral is mathlib's Riemannian length for the bundle
structure determined by the same specified metric. -/
theorem pathELength_eq_native (g : SmoothMetric n M₂) (γ : ℝ → M₂) (a b : ℝ) :
    letI : RiemannianBundle (fun x : M₂ => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
    pathELength J γ a b = nativePathLength g γ a b := by
  let _ : RiemannianBundle (fun x : M₂ => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  unfold nativePathLength
  apply lintegral_congr
  intro t
  let v := mfderiv R J γ t (1 : ℝ)
  have h : g.inner (γ t) v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  change ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner (γ t) v v))
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), ofReal_norm]

/-- A smooth local metric isometry preserves lengths of curves that
stay in its source. -/
theorem nativePathLength_comp_isometry
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    {γ : ℝ → M₂} {a b : ℝ}
    (hγ : ContMDiffOn R J 1 γ (Icc a b)) (hMap : MapsTo γ (Icc a b) e.source) :
    nativePathLength g₁ (e ∘ γ) a b = nativePathLength g₂ γ a b := by
  unfold nativePathLength
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hγD : MDifferentiableAt R J γ t :=
    (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt (by simp)
  have heD : MDifferentiableAt J J e (γ t) :=
    (he.smooth.contMDiffAt (e.open_source.mem_nhds (hMap ht'))).mdifferentiableAt (by simp)
  change ENNReal.ofReal (Real.sqrt (g₁.inner (e (γ t))
    (mfderiv R J (e ∘ γ) t 1) (mfderiv R J (e ∘ γ) t 1))) = _
  rw [mfderiv_comp t heD hγD]
  exact congrArg (fun x : ℝ => ENNReal.ofReal (Real.sqrt x))
    (he.metric_eq (γ t) (hMap ht') (mfderiv R J γ t 1) (mfderiv R J γ t 1)).symm

/-- The smooth local inverse of a metric isometry transports the tangent
metric back across the same open match. -/
theorem IsLocalMetricIsometry.symm
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e) :
    IsLocalMetricIsometry g₂ g₁ e.symm := by
  refine ⟨he.smooth_inverse, he.smooth, ?_⟩
  intro q hq v w
  let p := e.symm q
  let D := mfderiv J J e p
  let A := mfderiv J J e.symm q
  have hD : e.MDifferentiable J J :=
    ⟨he.smooth.mdifferentiableOn (by simp), he.smooth_inverse.mdifferentiableOn (by simp)⟩
  have hDA (t : X n) : D (A t) = t :=
    congrArg (fun L : X n →L[ℝ] X n => L t) (hD.comp_symm_deriv hq)
  calc
    _ = g₁.inner (e p) v w :=
      congrArg (fun y : M₁ => g₁.inner y v w) (e.right_inv hq).symm
    _ = g₁.inner (e p) (D (A v)) (D (A w)) :=
      congrArg₂ (fun x y : X n => g₁.inner (e p) x y) (hDA v).symm (hDA w).symm
    _ = _ := (he.metric_eq p (e.map_target hq) (A v) (A w)).symm

end CalderonPatch
