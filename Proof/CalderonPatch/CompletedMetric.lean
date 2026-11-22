module

public import Proof.CalderonPatch.InteriorPathLength
public import Proof.CalderonPatch.ConnectedInterior

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n

/-- The squared length of a tangent vector is continuous on the total
space of the tangent bundle. -/
theorem continuous_metricDiagonal (g : SmoothMetric n M₂) :
    Continuous (fun w : TangentBundle J M₂ => g.inner w.1 w.2 w.2) := by
  let _ : RiemannianBundle (fun x : M₂ => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle (X n) (fun x : M₂ => TangentSpace J x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have h : Continuous (fun w : TangentBundle J M₂ => (w.2 : TangentBundle J M₂)) := continuous_id
  exact h.inner_bundle h

/-- Once the extension is smooth through the boundary, its metric
identity follows by continuity on the tangent bundle and polarization. -/
theorem pullbackMetric_of_interior_agreement
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (𝓡∂ n).interior M₂) {f : M₂ → M₁}
    (hf : ContMDiff J J ∞ f) (hEq : EqOn f e e.source) :
    ∀ p (v w : TangentSpace J p), g₂.inner p v w =
      g₁.inner (f p) (mfderiv J J f p v) (mfderiv J J f p w) := by
  let A : TangentBundle J M₂ → ℝ := fun u => g₂.inner u.1 u.2 u.2
  let B : TangentBundle J M₂ → ℝ := (fun u : TangentBundle J M₁ => g₁.inner u.1 u.2 u.2) ∘
    tangentMap J J f
  have hA : Continuous A := continuous_metricDiagonal g₂
  have hB : Continuous B := (continuous_metricDiagonal g₁).comp (hf.continuous_tangentMap (by simp))
  let U : Set (TangentBundle J M₂) :=
    (Bundle.TotalSpace.proj : TangentBundle J M₂ → M₂) ⁻¹' e.source
  have hDense : Dense U := by
    have h := hs.symm ▸ (dense_manifoldInterior (n := n) (M := M₂))
    exact h.preimage (FiberBundle.isOpenMap_proj (X n) (fun p : M₂ => TangentSpace J p))
  have hClosed : IsClosed {u | A u = B u} := isClosed_eq hA hB
  have hSub : U ⊆ {u | A u = B u} := by
    intro u hu
    have hp : u.1 ∈ e.source := hu
    have hFE : f =ᶠ[𝓝 u.1] e :=
      Filter.mem_of_superset (e.open_source.mem_nhds hp) (fun _ hx => hEq hx)
    let D := mfderiv J J e u.1
    have hD : (mfderiv J J f u.1 u.2 : X n) = D u.2 :=
      congrArg (fun L : X n →L[ℝ] X n => L u.2) hFE.mfderiv_eq
    change g₂.inner u.1 u.2 u.2 = g₁.inner (f u.1) (mfderiv J J f u.1 u.2) (mfderiv J J f u.1 u.2)
    calc
      _ = g₁.inner (e u.1) (D u.2) (D u.2) := he.metric_eq u.1 hp u.2 u.2
      _ = g₁.inner (f u.1) (D u.2) (D u.2) :=
        congrArg (fun y : M₁ => g₁.inner y (D u.2) (D u.2)) (hEq hp).symm
      _ = _ := congrArg (fun v : X n => g₁.inner (f u.1) v v) hD.symm
  have hDiag (p : M₂) (v : TangentSpace J p) :
      g₂.inner p v v = g₁.inner (f p) (mfderiv J J f p v) (mfderiv J J f p v) :=
    closure_minimal hSub hClosed (hDense ⟨p,v⟩)
  intro p v w
  have hsum := hDiag p (v + w)
  have hv := hDiag p v
  have hw := hDiag p w
  simp only [map_add, ContinuousLinearMap.add_apply, g₂.symm p w v,
    g₁.symm (f p) (mfderiv J J f p w) (mfderiv J J f p v)] at hsum
  linarith

end CalderonPatch
