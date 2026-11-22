module

public import Proof.CalderonPatch.NormalChartFunctions
public import Proof.CalderonPatch.NormalChartInterior

import Proof.CalderonN.ChartGeometry
import Proof.CalderonPatch.MetricVolumeFinite
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X laplace laplace_congrOn)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace n

private theorem exists_local_smooth_laplace
    (g : SmoothMetric n M) {u : M → ℝ} (hu : ContMDiff J R ∞ u) (p : M) :
    ∃ A : Set M, IsOpen A ∧ p ∈ A ∧ ∃ v : M → ℝ, ContMDiffOn J R ∞ v A ∧
      EqOn v (nativeLaplace g u) (A ∩ (J).interior M) := by
  by_cases hp : p ∈ (J).interior M
  · obtain ⟨e,hpe,_,heI,he,hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
    let v := laplace (coordinateMetric g e) (u ∘ e.symm)
    have hv : ContDiffOn ℝ ∞ v e.target := contDiffOn_coordinateLaplace e.open_target
      (coordinateMetric_smooth g e he hes) (hu.comp_contMDiffOn hes).contDiffOn
    refine ⟨e.source,e.open_source,hpe,v ∘ e,hv.contMDiffOn.comp he e.mapsTo,?_⟩
    exact fun x hx => (nativeLaplace_eq_coordinate g e heI he hes hu.contMDiffOn hx.1).symm
  have hpB : p ∈ (J).boundary M := by
    rw [← (J).compl_interior]
    exact hp
  obtain ⟨D⟩ := exists_nativeBoundaryMetricChart g p hpB
  have hpD : D.coord p ∈ D.ambient :=
    (D.target_eq ▸ D.coord.map_source D.point_source : _ ∈ D.ambient ∩ H).1
  obtain ⟨u₀,V,hu₀,hV,hpV,hVD,hU⟩ := D.exists_smooth_function_extension hu isCompact_singleton
    (singleton_subset_iff.mpr hpD)
  let A := D.coord.source ∩ D.coord ⁻¹' V
  let f := laplace D.field u₀
  have hA : IsOpen A := D.smooth.continuousOn.isOpen_inter_preimage D.open_source hV
  have hf : ContDiffOn ℝ ∞ f V := contDiffOn_coordinateLaplace hV
    ⟨fun i j => (D.smooth_field.1 i j).mono hVD,fun x hx => D.smooth_field.2 x (hVD hx)⟩ hu₀.contDiffOn
  obtain ⟨e,hET,hEF,hEI,heI,he,hes,hMetric⟩ := D.exists_interior_restriction hV hVD
  refine ⟨A,hA,⟨D.point_source,hpV (mem_singleton _)⟩,f ∘ D.coord,
    hf.contMDiffOn.comp (D.smooth.mono inter_subset_left) (fun _ hx => hx.2),?_⟩
  intro x hx
  have hZ : D.coord x ∈ e.target := hET.symm ▸ ⟨hx.1.2,
    (D.interior_iff x hx.1.1).mp hx.2⟩
  have hS := e.map_target hZ
  rw [hEI,D.coord.left_inv hx.1.1] at hS
  have hEq : EqOn (u ∘ e.symm) u₀ e.target := by
    rw [hEI,hET]
    exact hU.symm.mono (inter_subset_inter_right V positiveHalfSpace_subset_inwardHalfSpace)
  rw [nativeLaplace_eq_coordinate g e heI he hes hu.contMDiffOn hS,
    laplace_congrOn e.open_target hMetric hEq (e.map_source hS)]
  exact congrArg f (congrFun hEF x).symm

/-- The operator recorded at interior points has a smooth extension
through the native boundary for every smooth function. The extension is
unique by density of the interior. -/
theorem exists_smooth_nativeLaplace (g : SmoothMetric n M) {u : M → ℝ}
    (hu : ContMDiff J R ∞ u) :
    ∃ v : M → ℝ, ContMDiff J R ∞ v ∧ EqOn v (nativeLaplace g u) ((J).interior M) := by
  classical
  choose A hA hMem v hv hEq using exists_local_smooth_laplace g hu
  let w (x : M) := v x x
  refine ⟨w,?_ ,fun _ hx => hEq _ ⟨hMem _,hx⟩⟩
  intro x
  refine ((hv x x (hMem x)).contMDiffAt ((hA x).mem_nhds (hMem x))).congr_of_eventuallyEq ?_
  filter_upwards [(hA x).mem_nhds (hMem x)] with y hy
  let B := A x ∩ A y
  let S := B ∩ (J).interior M
  have hB : IsOpen B := (hA x).inter (hA y)
  have hDense : B ⊆ closure S := by
    simpa only [B,S,inter_comm] using
      (dense_manifoldInterior (n := n) (M := M)).open_subset_closure_inter hB
  have hEq' : EqOn (v y) (v x) S := fun z hz =>
    (hEq y ⟨hz.1.2,hz.2⟩).trans (hEq x ⟨hz.1.1,hz.2⟩).symm
  exact hEq'.of_subset_closure ((hv y).continuousOn.mono inter_subset_right)
    ((hv x).continuousOn.mono inter_subset_left) inter_subset_left hDense ⟨hy,hMem y⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The native interior convention and its smooth extension agree
almost everywhere for the canonical metric volume. -/
theorem nativeLaplace_memLp_two (g : SmoothMetric n M) (μ : Measure M)
    (hμ : IsMetricVolume g μ) {u : M → ℝ} (hu : ContMDiff J R ∞ u) :
    MemLp (nativeLaplace g u) 2 μ := by
  let : IsFiniteMeasure μ := hμ.isFiniteMeasure
  obtain ⟨v,hv,hEq⟩ := exists_smooth_nativeLaplace g hu
  have hI : ∀ᵐ x ∂μ, x ∈ (J).interior M := by
    rw [ae_iff]
    change μ (((J).interior M)ᶜ) = 0
    rw [(J).compl_interior]
    exact metricVolume_boundary_eq_zero g μ hμ
  exact (hv.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).ae_eq
    (hI.mono fun _ hx => hEq hx)

end CalderonPatch
