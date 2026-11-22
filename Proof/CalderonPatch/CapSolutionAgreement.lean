module

public import Proof.CalderonPatch.CommonSignedCapCharts
public import Proof.CalderonPatch.CapSeamFlux
public import Proof.CalderonPatch.InteriorIsometryNaturality

import Proof.CalderonPatch.NativeInverseRegularityProof
import Proof.CalderonPatch.SmoothDirichletFromForcing
import Proof.CalderonN.HarmonicL2Space
import Mathlib.Tactic

public section
noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X laplace laplace_congrOn)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (n+1)
local notation "E" => X N
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

variable {d₁ d₂ : DirichletData n M} {Γ : Set ((𝓡∂ (n+1)).boundary M)}
  {C : MeasuredCommonCap d₁ d₂ Γ}

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] in
private theorem harm_pullback_of_cap
    {g G : SmoothMetric N M} {cap : Set M} (O : OriginalCopy g G cap) {w : M → ℝ}
    (hw : ContMDiff J R ∞ w)
    (hZero : EqOn (nativeLaplace G w) 0 ((J).interior M \ closure cap)) :
    EqOn (nativeLaplace g (w ∘ O.embed)) 0 ((J).interior M) := by
  obtain ⟨e,heS,heT,heE,_,he⟩ := O.exists_interiorIsometry
  intro x hx
  have hxE : x ∈ e.source := heS.symm ▸ hx
  have hn := nativeLaplace_comp_localIsometry he (heS.symm ▸ Subset.rfl)
    (heT.symm ▸ sdiff_subset) hw.contMDiffOn hxE
  have hN := hn.trans (hZero (heT ▸ e.map_source hxE))
  rwa [heE] at hN

private theorem smooth_dirichlet (D : DirichletData n M) (v : M → ℝ) (hv : ContMDiff J R ∞ v) :
    ∃ w : M → ℝ, ContMDiff J R ∞ w ∧ EqOn w v ((J).boundary M) ∧
      EqOn (nativeLaplace D.metric w) 0 ((J).interior M) := by
  apply exists_dirichletHarmonic_from_smoothForcing D _ hv
  intro f q hq hEq
  obtain ⟨w,hw,hw0,hwQ,_⟩ := (nativeInverseRegularity D).smooth_solution f q hq hEq
  exact ⟨w,hw,hw0,hwQ⟩

/-- Smooth zero-boundary inverse solutions on the extensions agree
on the common cap when their forcing agrees there and vanishes in
the original interiors. -/
theorem MeasuredCommonCap.cap_solution_agreement
    (S : C.SignedInteriorCharts)
    (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {w₁ w₂ : M → ℝ}
    (hw₁ : ContMDiff J R ∞ w₁) (hw₂ : ContMDiff J R ∞ w₂)
    (h₀₁ : EqOn w₁ 0 ((J).boundary M)) (h₀₂ : EqOn w₂ 0 ((J).boundary M))
    (hH₁ : EqOn (nativeLaplace C.firstMetric w₁) 0 ((J).interior M \ closure C.capMap.target))
    (hH₂ : EqOn (nativeLaplace C.secondMetric w₂) 0 ((J).interior M \ closure C.capMap.source))
    (hCap : EqOn ((nativeLaplace C.firstMetric w₁) ∘ C.capMap) (nativeLaplace C.secondMetric w₂)
      C.capMap.source) :
    EqOn (w₁ ∘ C.capMap) w₂ C.capMap.source := by
  obtain ⟨D⟩ := C.exists_scalarReadings hw₁ hw₂
  let W := signedCap C.signedHeight
  let g₁ := C.coordinates.first.field
  let g₂ := C.coordinates.second.field
  let δ := D.first - D.second
  have hW : IsOpen W := C.isOpen_signedCap
  have hWU : W ⊆ D.domain := C.signedCap_subset_box.trans D.box_subset
  have hA (x : E) (hx : x ∈ W) : 0 ≤ (C.pushedPoint x).2 :=
    ((C.signedCap_push_iff x).mpr hx).1.le
  have hR₁ : EqOn D.first (w₁ ∘ S.first.symm) W := by
    intro x hx
    rw [S.first_inverse]
    exact D.reads_first ⟨hWU hx,hA x hx⟩
  have hR₂ : EqOn D.second (w₂ ∘ S.second.symm) W := by
    intro x hx
    rw [S.second_inverse]
    exact D.reads_second ⟨hWU hx,hA x hx⟩
  have hEq₁ (x : E) (hx : x ∈ W) :
      laplace g₁ D.first x = nativeLaplace C.firstMetric w₁ (S.first.symm x) := by
    have hxT : x ∈ S.first.target := S.first_target.symm ▸ hx
    have hN := nativeLaplace_eq_coordinate C.firstMetric S.first S.first_interior
      S.first_smooth S.first_inverse_smooth hw₁.contMDiffOn (S.first.map_target hxT)
    rw [S.first.right_inv hxT] at hN
    exact (laplace_congrOn hW S.first_field.symm hR₁ hx).trans hN.symm
  have hEq₂ (x : E) (hx : x ∈ W) :
      laplace g₂ D.second x = nativeLaplace C.secondMetric w₂ (S.second.symm x) := by
    have hxT : x ∈ S.second.target := S.second_target.symm ▸ hx
    have hN := nativeLaplace_eq_coordinate C.secondMetric S.second S.second_interior
      S.second_smooth S.second_inverse_smooth hw₂.contMDiffOn (S.second.map_target hxT)
    rw [S.second.right_inv hxT] at hN
    exact (laplace_congrOn hW S.second_field.symm hR₂ hx).trans hN.symm
  have hShared : EqOn g₁ g₂ W := fun x hx => C.coordinates.fields_eq (fun hH => (not_le_of_gt hx.2) hH)
  have hDelta : EqOn (laplace g₁ δ) 0 (W ∩ D.domain) := by
    intro x hx
    have hxT : x ∈ S.second.target := S.second_target.symm ▸ hx.1
    have hxS : S.second.symm x ∈ C.capMap.source := S.second_source ▸ S.second.map_target hxT
    have hCap' : nativeLaplace C.firstMetric w₁ (S.first.symm x) =
        nativeLaplace C.secondMetric w₂ (S.second.symm x) := by
      rw [S.same_inverse hx.1]
      exact hCap hxS
    change laplace g₁ (fun y => D.first y - D.second y) x = 0
    rw [CalderonN.laplace_sub hW g₁ D.smooth_first.contDiffOn D.smooth_second.contDiffOn hx.1,
      laplace_congrOn hW hShared (fun _ _ => rfl : EqOn D.second D.second W) hx.1,
      hEq₁ x hx.1,hEq₂ x hx.1,hCap',sub_self]
  have hFlux := D.truncated_seamFlux_nonpos hMeas hw₁ hw₂ h₀₁ h₀₂
    (harm_pullback_of_cap C.firstCopy hw₁ hH₁) (harm_pullback_of_cap C.secondCopy hw₂ hH₂)
    (smooth_dirichlet d₁) (smooth_dirichlet d₂)
  have hg : CalderonN.SmoothMetric D.domain g₁ :=
    ⟨fun i j => (C.coordinates.first.smooth_field.1 i j).mono D.domain_subset,
      fun x hx => C.coordinates.first.smooth_field.2 x (D.domain_subset hx)⟩
  have hδ := eqOn_zero_signedCap_of_truncatedFlux C.lower_le_capUpper C.capUpper_normal D.open_domain
    (C.mapsTo_capBox D.box_subset) C.signedHeight_contDiff.continuous C.signedHeight_bounds
    (by rw [C.tangentialBox_cap]; obtain ⟨_,_,h₁,h₂⟩ := C.exists_compact_signedHeight_support; exact h₁.trans h₂)
    hg (D.smooth_first.sub D.smooth_second).contDiffOn
    (fun _ hx hg' => D.sub_zero_on_graph h₀₁ h₀₂ hx hg') hDelta hFlux
  intro p hp
  have hpS : p ∈ S.second.source := S.second_source.symm ▸ hp
  let x := S.second p
  have hx : x ∈ signedCap C.signedHeight := S.second_target ▸ S.second.map_source hpS
  have hEq : D.first x = D.second x := sub_eq_zero.mp (hδ hx)
  rw [hR₁ hx,hR₂ hx,Function.comp_apply,Function.comp_apply,S.same_inverse hx,
    Function.comp_apply,S.second.left_inv hpS] at hEq
  exact hEq

end CalderonPatch
