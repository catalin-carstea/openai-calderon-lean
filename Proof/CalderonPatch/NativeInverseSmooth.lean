module

public import Proof.CalderonPatch.NativeWeakClassicalEquation

import Proof.CalderonPatch.InteriorChartHigher
import Proof.CalderonPatch.NormalChartSmooth
import Proof.CalderonPatch.NativeRepresentativeGluing

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- Local smooth representatives of the actual weak inverse, with
zero trace on the native boundary and the classical source equation. -/
theorem nativeWeakInverse_smooth_on
    (D : DirichletData m M) {U : Set M} (hU : IsOpen U)
    (f : Lp ℝ 2 D.volume) {q : M → ℝ} (hq : ContMDiff J R ∞ q)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U] q) :
    ∃ u : M → ℝ, ContMDiffOn J R ∞ u U ∧ EqOn u 0 (U ∩ (J).boundary M) ∧
      EqOn (-nativeLaplace D.metric u) q (U ∩ (J).interior M) ∧
      (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict U] u := by
  have hLoc (p : M) (hp : p ∈ U) :
      ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
        ∃ u : M → ℝ, ContMDiffOn J R ∞ u V ∧ EqOn u 0 (V ∩ (J).boundary M) ∧
          (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict V] u := by
    by_cases hpB : p ∈ (J).boundary M
    · exact exists_weakInverse_boundary_smooth_rep D hU hp hpB f hq hf
    · have hpI := ((J).isInteriorPoint_iff_not_isBoundaryPoint p).2 hpB
      obtain ⟨V,hV,hpV,hVU,u,hu,hValue⟩ := exists_weakInverse_interior_smooth_rep D hU hp hpI f hq hf
      exact ⟨V,hV,hpV,hVU.trans inter_subset_left,u,hu,fun x hx =>
        (((J).isInteriorPoint_iff_not_isBoundaryPoint x).1 (hVU hx.1).2 hx.2).elim,hValue⟩
  obtain ⟨u,hu,hu₀,hValue⟩ := exists_smooth_zero_trace_ae_eq_of_locally D hU hLoc
  exact ⟨u,hu,hu₀,nativeLaplace_eq_of_weakDirichletInverse_smooth_value D hU f hq hf hu hValue,hValue⟩

/-- Smooth native forcing gives a smooth zero-boundary solution of
the positive Laplace–Beltrami equation in the weak inverse's own class. -/
theorem nativeWeakInverse_smooth_solution (D : DirichletData m M)
    (f : Lp ℝ 2 D.volume) (q : M → ℝ) (hq : ContMDiff J R ∞ q)
    (hf : (f : M → ℝ) =ᵐ[D.volume] q) :
    ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ EqOn u 0 ((J).boundary M) ∧
      EqOn (-nativeLaplace D.metric u) q ((J).interior M) ∧
      (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume] u := by
  simpa only [Measure.restrict_univ,contMDiffOn_univ,univ_inter] using
    nativeWeakInverse_smooth_on D isOpen_univ f hq (by simpa only [Measure.restrict_univ] using hf)

/-- Where its forcing vanishes, the native weak inverse is harmonic
and smooth up to any part of the boundary met by the open set. -/
theorem nativeWeakInverse_local_zero_forcing (D : DirichletData m M)
    (U : Set M) (hU : IsOpen U) (f : Lp ℝ 2 D.volume)
    (hf : (f : M → ℝ) =ᵐ[D.volume.restrict U] 0) :
    ∃ u : M → ℝ, ContMDiffOn J R ∞ u U ∧ EqOn u 0 (U ∩ (J).boundary M) ∧
      EqOn (nativeLaplace D.metric u) 0 (U ∩ (J).interior M) ∧
      (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict U] u := by
  obtain ⟨u,hu,hZero,hEq,hValue⟩ :=
    nativeWeakInverse_smooth_on D hU f (contMDiff_const (c := (0 : ℝ))) hf
  exact ⟨u,hu,hZero,fun x hx => neg_eq_zero.mp (hEq hx),hValue⟩

end CalderonPatch
