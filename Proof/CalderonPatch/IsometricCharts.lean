module

public import Proof.CalderonPatch.ChartDensity

@[expose] public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X axis)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)

/-- If two inverse charts identify the same points under a local isometry,
then their native coefficient matrices coincide on the open common target. -/
theorem coordinateMetric_eq_of_isometry {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {Φ : OpenPartialHomeomorph M₂ M₁} (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    {a : OpenPartialHomeomorph M₁ (X n)} {b : OpenPartialHomeomorph M₂ (X n)}
    (hb : ContMDiffOn K J ∞ b.symm b.target)
    {V : Set (X n)} (hV : IsOpen V) (hVb : V ⊆ b.target)
    (hVΦ : MapsTo b.symm V Φ.source) (hEq : EqOn a.symm (Φ ∘ b.symm) V) :
    EqOn (coordinateMetric g₁ a) (coordinateMetric g₂ b) V := by
  intro x hx
  have hbD := (hb.contMDiffAt (b.open_target.mem_nhds (hVb hx))).mdifferentiableAt (by simp)
  have hΦD := (hΦ.smooth.contMDiffAt (Φ.open_source.mem_nhds (hVΦ hx))).mdifferentiableAt (by simp)
  have hE : (a.symm : X n → M₁) =ᶠ[𝓝 x] (Φ ∘ b.symm) :=
    Filter.mem_of_superset (hV.mem_nhds hx) (fun _ hy => hEq hy)
  let Da : X n →L[ℝ] X n := mfderiv K J a.symm x
  let Db : X n →L[ℝ] X n := mfderiv K J b.symm x
  let DΦ : X n →L[ℝ] X n := mfderiv J J Φ (b.symm x)
  have hD : Da = DΦ.comp Db := hE.mfderiv_eq.trans (mfderiv_comp x hΦD hbD)
  ext i j
  change g₁.inner (a.symm x) (Da (axis i)) (Da (axis j)) =
    g₂.inner (b.symm x) (Db (axis i)) (Db (axis j))
  rw [hD]
  calc
    _ = g₁.inner (Φ (b.symm x)) (DΦ (Db (axis i))) (DΦ (Db (axis j))) :=
      congrArg (fun q : M₁ => g₁.inner q (DΦ (Db (axis i))) (DΦ (Db (axis j)))) (hEq hx)
    _ = _ := (hΦ.metric_eq (b.symm x) (hVΦ hx) _ _).symm

/-- Transport a chart along a local isometry, keeping its whole coordinate
target and the metric on it. -/
theorem exists_transported_chart {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {Φ : OpenPartialHomeomorph M₂ M₁} (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    (b : OpenPartialHomeomorph M₂ (X n)) (hbΦ : b.source ⊆ Φ.source)
    (hb : ContMDiffOn J K ∞ b b.source) (hbs : ContMDiffOn K J ∞ b.symm b.target) :
    ∃ a : OpenPartialHomeomorph M₁ (X n), a.target = b.target ∧
      a.source = Φ '' b.source ∧ (a.symm : X n → M₁) = (Φ ∘ b.symm) ∧
      ContMDiffOn J K ∞ a a.source ∧ ContMDiffOn K J ∞ a.symm a.target ∧
      EqOn (coordinateMetric g₁ a) (coordinateMetric g₂ b) b.target := by
  let a := Φ.symm.trans b
  have hT : a.target = b.target := inter_eq_left.mpr (fun x hx => hbΦ (b.map_target hx))
  have hS : a.source = Φ '' b.source := by
    ext y
    constructor
    · intro hy
      exact ⟨Φ.symm y, hy.2, Φ.right_inv hy.1⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨Φ.map_source (hbΦ hp), ?_⟩
      change Φ.symm (Φ p) ∈ b.source
      rwa [Φ.left_inv (hbΦ hp)]
  refine ⟨a, hT, hS, rfl, ?_, ?_, ?_⟩
  · exact hb.comp (hΦ.smooth_inverse.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  · rw [hT]
    exact hΦ.smooth.comp hbs (fun _ hx => hbΦ (b.map_target hx))
  · exact coordinateMetric_eq_of_isometry hΦ hbs b.open_target Subset.rfl
      (fun _ hx => hbΦ (b.map_target hx)) (fun _ _ => rfl)

end CalderonPatch
