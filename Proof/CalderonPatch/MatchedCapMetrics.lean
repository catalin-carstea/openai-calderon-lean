module

public import Proof.CalderonPatch.CapMetricReplacement
public import Proof.CalderonPatch.NativeBoundaryMetricChart
public import Proof.CalderonPatch.SmoothPasting

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X MetricField)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "TangentPlane" => boundaryTangentPlane (0 : I n)
local notation "H" => inwardHalfSpace n

/-- Restrict a product boundary chart to a smaller open signed domain. -/
@[expose] def ProductBoundaryChart.restrictAmbient
    (D : ProductBoundaryChart (n := n) (M := M) (Z := TangentPlane))
    {W : Set (TangentPlane × ℝ)} (hW : IsOpen W) (hWD : W ⊆ D.ambient) :
    ProductBoundaryChart (n := n) (M := M) (Z := TangentPlane) := by
  let c := D.coord
  let U := c.source ∩ c ⁻¹' W
  let V := W ∩ (univ ×ˢ Ici (0 : ℝ))
  have hV : V ⊆ c.target := D.target_eq.symm ▸ inter_subset_inter_left _ hWD
  let d : PartialEquiv M (TangentPlane × ℝ) :=
    { toFun := c
      invFun := c.symm
      source := U
      target := V
      map_source' := fun x hx => ⟨hx.2,(D.target_eq ▸ c.map_source hx.1 : _ ∈ D.ambient ∩ _).2⟩
      map_target' := fun x hx => ⟨c.map_target (hV hx), by
        change c (c.symm x) ∈ W
        rw [c.right_inv (hV hx)]
        exact hx.1⟩
      left_inv' := fun x hx => c.left_inv hx.1
      right_inv' := fun x hx => c.right_inv (hV hx) }
  have hU : IsOpen U := D.smooth.continuousOn.isOpen_inter_preimage D.open_source hW
  exact ⟨d,hU,W,hW,rfl,D.smooth.mono inter_subset_left,D.smooth_inverse.mono hV,
    fun x hx => D.interior_iff x hx.1⟩

/-- Smooth metrics with matching signed jets have smooth extensions
that are common on the exterior side. The two originals are kept on
the full inward half space. -/
theorem exists_matched_signed_metric_extensions
    {V : Set (X n)} (hV : IsOpen V) {g₁ g₂ : MetricField n}
    (h₁ : CalderonN.SmoothMetric V g₁) (h₂ : CalderonN.SmoothMetric V g₂)
    (hJets : ∀ (i j : I n) (k : ℕ), EqOn
      (iteratedFDeriv ℝ k (fun x => g₁ x i j)) (iteratedFDeriv ℝ k (fun x => g₂ x i j))
      (V ∩ {x | x (0 : I n) = 0})) :
    ∃ G₁ G₂ : MetricField n, CalderonN.SmoothMetric V G₁ ∧ CalderonN.SmoothMetric V G₂ ∧
      EqOn G₁ g₁ H ∧ EqOn G₂ g₂ H ∧ EqOn G₁ G₂ Hᶜ := by
  classical
  let G₂ := (H).piecewise g₂ g₁
  have hS : frontier H = {x | x (0 : I n) = 0} := by
    change frontier {x : X n | 0 ≤ x (0 : I n)} = _
    rw [frontier_halfSpace 2 (0 : ℝ) (0 : I n)]
    ext x
    exact eq_comm
  have hM (i j : I n) : ContDiffOn ℝ ∞ (fun x => G₂ x i j) V := by
    have hPiece := contDiffOn_piecewise_of_matched_jets (S := H) hV (h₂.1 i j) (h₁.1 i j)
      (fun k x hx => (hJets i j k (by rwa [hS] at hx)).symm)
    apply hPiece.congr
    intro x _
    by_cases hx : x ∈ H <;> simp [G₂,hx]
  refine ⟨g₁,G₂,h₁,⟨hM,?_⟩,fun _ _ => rfl,
    fun x hx => piecewise_eq_of_mem _ _ _ hx, fun x hx => (piecewise_eq_of_notMem _ _ _ hx).symm⟩
  intro x hx
  by_cases hh : x ∈ H
  · change (G₂ x).PosDef
    rw [show G₂ x = g₂ x from piecewise_eq_of_mem H g₂ g₁ hh]
    exact h₂.2 x hx
  · change (G₂ x).PosDef
    rw [show G₂ x = g₁ x from piecewise_eq_of_notMem H g₂ g₁ hh]
    exact h₁.2 x hx

end CalderonPatch
