module

public import Proof.CalderonPatch.MeasuredBoundaryJets
public import Proof.CalderonPatch.PairedNativeBoundaryBox
public import Proof.CalderonPatch.AttachedCommonCap

import Mathlib.Tactic

public section
noncomputable section
open Filter Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X chartDerivativeWord)
open BoundaryLayer (normalMetricJets_eqOn_of_patchEnergy normalJetAt_eq_chartDerivativeWord)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Z" => X (n+1)
local notation "Y" => X n
local notation "J" => 𝓡∂ (n+1)
local notation "L" => (inwardChartSplit (n := n+1))
local notation "P" => boundaryTangentPlane (0 : I (n+1)) × ℝ

/-- A common cap recovered from the measurements, retaining the source
normal charts for the boundary Green formula. -/
structure MeasuredCommonCap (d₁ d₂ : DirichletData n M) (Γ : Set ((J).boundary M)) where
  center : (J).boundary M
  charts : PairedNativeBoundaryBox d₁.metric d₂.metric Γ center
  ambient : Set P
  open_ambient : IsOpen ambient
  subset_first : ambient ⊆ charts.prod₁.ambient
  subset_second : ambient ⊆ charts.prod₂.ambient
  subset_signed : L ⁻¹' ambient ⊆ charts.signed
  firstMetric : SmoothMetric (n+1) M
  secondMetric : SmoothMetric (n+1) M
  capMap : OpenPartialHomeomorph M M
  connected_source : IsConnected capMap.source
  connected_target : IsConnected capMap.target
  source_interior : capMap.source ⊆ (J).interior M
  target_interior : capMap.target ⊆ (J).interior M
  isometry : IsLocalMetricIsometry firstMetric secondMetric capMap
  firstCopy : OriginalCopy d₁.metric firstMetric capMap.target
  secondCopy : OriginalCopy d₂.metric secondMetric capMap.source
  patch : Set ((J).boundary M)
  open_patch : IsOpen patch
  nonempty_patch : patch.Nonempty
  patch_subset : patch ⊆ Γ
  traces_supported : ∀ w : M → ℝ, EqOn w 0 ((J).boundary M) →
    tsupport (fun p : (J).boundary M => w (firstCopy.embed p)) ⊆ Γ ∧
    tsupport (fun p : (J).boundary M => w (secondCopy.embed p)) ⊆ Γ
  seam : ∀ e : OpenPartialHomeomorph M M, e.source = (J).interior M → EqOn e capMap capMap.source →
    ∀ p ∈ patch, secondCopy.embed p ∈ e.source ∧ e (secondCopy.embed p) = firstCopy.embed p
  coordinates : CommonCapCoordinates (W := ambient) (z₀ := (charts.prod₂.coord center).1)
    (charts.prod₁.restrictAmbient open_ambient subset_first)
    (charts.prod₂.restrictAmbient open_ambient subset_second) charts.first.field charts.second.field
    firstMetric secondMetric capMap firstCopy.embed secondCopy.embed

/-- Equal measured energies yield the actual smooth cap extensions
and their open cap isometry. The original embeddings carry zero trace
on the extended boundary back to supported trace on the measured patch. -/
theorem exists_attached_commonCap_of_patchEnergy (hn : 2 ≤ n)
    (d₁ d₂ : DirichletData n M) {Γ : Set ((J).boundary M)}
    (hΓ : IsOpen Γ) (hΓn : Γ.Nonempty)
    (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ) :
    Nonempty (MeasuredCommonCap d₁ d₂ Γ) := by
  obtain ⟨p,hp⟩ := hΓn
  obtain ⟨D⟩ := exists_pairedNativeBoundaryBox d₁.metric d₂.metric hΓ hp
  let U : Set Y := normalFacePoint ⁻¹' D.signed
  have hU : IsOpen U := D.open_signed.preimage continuous_normalFacePoint
  have hU₁ : MapsTo normalFacePoint U D.first.ambient := fun y hy => D.signed₁ hy
  have hU₂ : MapsTo normalFacePoint U D.second.ambient := fun y hy => D.signed₂ hy
  have hQU : MapsTo (WithLp.toLp 2)
      (Icc (D.boxLower ∘ Fin.succAbove 0) (D.boxUpper ∘ Fin.succAbove 0)) U := by
    intro z hz
    have hZ : WithLp.ofLp (normalFacePoint (WithLp.toLp 2 z)) ∈ Icc D.boxLower D.boxUpper :=
      normalFacePoint_in_closedBox D.lower_zero D.upper_pos.le hz
    have h := D.closed_box hZ
    rw [WithLp.toLp_ofLp] at h
    exact h
  let η : ContDiffBump (0 : ℝ) := ⟨D.boxUpper 0 / 4,D.boxUpper 0 / 2,
    by linarith only [D.upper_pos],by linarith only [D.upper_pos]⟩
  have hη : η.rOut < D.boxUpper 0 := by
    change D.boxUpper 0 / 2 < D.boxUpper 0
    linarith only [D.upper_pos]
  have hJets := normalMetricJets_eqOn_of_patchEnergy D.first D.second hn hMeas D.bounds
    D.lower_zero D.open_signed D.signed₁ D.signed₂ D.closed_box D.common_inverse D.face_patch
    hU hU₁ hU₂ hQU η hη
  let V : Set Z := D.signed ∩ normalTangentialCoordinates ⁻¹' tangentialBox D.boxLower D.boxUpper
  let W : Set P := (inwardChartSplit (n := n+1)).symm ⁻¹' V
  have hV : IsOpen V := D.open_signed.inter ((isOpen_tangentialBox _ _).preimage
    contDiff_normalTangentialCoordinates.continuous)
  have hW : IsOpen W := hV.preimage (inwardChartSplit (n := n+1)).symm.continuous
  have hWV (x : Z) : L x ∈ W ↔ x ∈ V := by
    change (inwardChartSplit (n := n+1)).symm (L x) ∈ V ↔ _
    rw [(inwardChartSplit (n := n+1)).symm_apply_apply]
  have hWD₁ : W ⊆ D.prod₁.ambient := by
    intro x hx
    have ht : (inwardChartSplit (n := n+1)).symm x ∈ D.first.ambient := D.signed₁ hx.1
    rw [D.ambient₁] at ht
    change L ((inwardChartSplit (n := n+1)).symm x) ∈ D.prod₁.ambient at ht
    rw [(inwardChartSplit (n := n+1)).apply_symm_apply] at ht
    exact ht
  have hWD₂ : W ⊆ D.prod₂.ambient := by
    intro x hx
    have ht := D.signed₂ (show (inwardChartSplit (n := n+1)).symm x ∈ D.signed from hx.1)
    rw [D.ambient₂,mem_preimage,(inwardChartSplit (n := n+1)).apply_symm_apply] at ht
    exact ht
  have hMem₁ (q : M) (h : D.prod₁.coord q ∈ W) : D.first.coord q ∈ D.signed := by
    have h' : (inwardChartSplit (n := n+1)).symm (D.prod₁.coord q) ∈ V := h
    rw [← show D.first.coord q = (inwardChartSplit (n := n+1)).symm (D.prod₁.coord q) from congrFun D.coord₁ q] at h'
    exact h'.1
  have hMem₂ (q : M) (h : D.prod₂.coord q ∈ W) : D.second.coord q ∈ D.signed := by
    have h' : (inwardChartSplit (n := n+1)).symm (D.prod₂.coord q) ∈ V := h
    rw [← show D.second.coord q = (inwardChartSplit (n := n+1)).symm (D.prod₂.coord q) from congrFun D.coord₂ q] at h'
    exact h'.1
  have hTrace₁ (q : (J).boundary M) (hq : (q : M) ∈ D.prod₁.coord.source)
      (hWq : D.prod₁.coord q ∈ W) : q ∈ Γ :=
    D.trace_first q (D.source₁.symm ▸ hq) (hMem₁ q hWq)
  have hCommon (q : (J).boundary M) (hq : (q : M) ∈ D.prod₂.coord.source)
      (hWq : D.prod₂.coord q ∈ W) :
      (q : M) ∈ D.prod₁.coord.source ∧ D.prod₁.coord q = D.prod₂.coord q ∧ q ∈ Γ := by
    obtain ⟨h1,h2,h3⟩ := D.trace_second q (D.source₂.symm ▸ hq) (hMem₂ q hWq)
    refine ⟨D.source₁ ▸ h1,(inwardChartSplit (n := n+1)).symm.injective ?_,h3⟩
    exact (congrFun D.coord₁ q).symm.trans (h2.trans (congrFun D.coord₂ q))
  have hpS : (p : M) ∈ D.prod₂.coord.source := D.source₂ ▸ D.second.point_source
  let z₀ := (D.prod₂.coord p).1
  have hpC : D.prod₂.coord p = (z₀,0) :=
    Prod.ext rfl (D.prod₂.height_eq_zero_on_boundary p.property hpS)
  have hpV : D.second.coord p ∈ V := ⟨D.center_signed,D.center_box⟩
  have hpW : (z₀,(0 : ℝ)) ∈ W := by
    rw [← hpC]
    change (inwardChartSplit (n := n+1)).symm (D.prod₂.coord p) ∈ V
    rw [← show D.second.coord p = (inwardChartSplit (n := n+1)).symm (D.prod₂.coord p)
      from congrFun D.coord₂ (p : M)]
    exact hpV
  have hDom₁ : L ⁻¹' W ⊆ D.first.ambient := fun x hx => D.signed₁ ((hWV x).mp hx).1
  have hDom₂ : L ⁻¹' W ⊆ D.second.ambient := fun x hx => D.signed₂ ((hWV x).mp hx).1
  have hNat₁ (x : M) (hx : x ∈ D.prod₁.coord.source) :
      nativeCoordinateBilinear D.first.field ((inwardChartSplit (n := n+1)).symm ∘ D.prod₁.coord) x = d₁.metric.inner x := by
    rw [← D.coord₁]
    ext v w
    rw [nativeCoordinateBilinear_apply]
    exact (D.first.realizes x (D.source₁.symm ▸ hx) v w).symm
  have hNat₂ (x : M) (hx : x ∈ D.prod₂.coord.source) :
      nativeCoordinateBilinear D.second.field ((inwardChartSplit (n := n+1)).symm ∘ D.prod₂.coord) x = d₂.metric.inner x := by
    rw [← D.coord₂]
    ext v w
    rw [nativeCoordinateBilinear_apply]
    exact (D.second.realizes x (D.source₂.symm ▸ hx) v w).symm
  have hMatched (i j : I (n+1)) (k : ℕ) : EqOn
      (chartDerivativeWord (List.replicate k 0) (fun x => D.first.field x i j))
      (chartDerivativeWord (List.replicate k 0) (fun x => D.second.field x i j))
      ((inwardChartSplit ⁻¹' W) ∩ {x | x (0 : I (n+1)) = 0}) := by
    intro x hx
    let y := normalTangentialCoordinates x
    have hy : y ∈ tangentialBox D.boxLower D.boxUpper := ((hWV x).mp hx.1).2
    have hY : normalFacePoint y = x := normalFacePoint_tangentialCoordinates hx.2
    have hy₁ : normalFacePoint y ∈ D.first.ambient := hY.symm ▸ hDom₁ hx.1
    have hy₂ : normalFacePoint y ∈ D.second.ambient := hY.symm ▸ hDom₂ hx.1
    have hRead := hJets k i j hy
    change BoundaryLayer.normalJetAt (fun z => D.first.field z i j) k y =
      BoundaryLayer.normalJetAt (fun z => D.second.field z i j) k y at hRead
    rw [normalJetAt_eq_chartDerivativeWord D.first.open_ambient (D.first.smooth_field.1 i j) hy₁,
      normalJetAt_eq_chartDerivativeWord D.second.open_ambient (D.second.smooth_field.1 i j) hy₂,hY] at hRead
    exact hRead
  obtain ⟨G₁,G₂,eCap,hCon₂,hCon₁,hI₂,hI₁,hIso,O₁,O₂,patch,hP,hPn,hPg,hT,hSeam,⟨C⟩⟩ :=
    exists_attached_commonCap_of_matched_jets d₁.metric d₂.metric D.prod₁ D.prod₂ hW hWD₁ hWD₂
      z₀ hpW p hpS hpC hTrace₁ hCommon
      ⟨fun i j => (D.first.smooth_field.1 i j).mono hDom₁, fun x hx => D.first.smooth_field.2 x (hDom₁ hx)⟩
      ⟨fun i j => (D.second.smooth_field.1 i j).mono hDom₂, fun x hx => D.second.smooth_field.2 x (hDom₂ hx)⟩
      hNat₁ hNat₂ hMatched
  exact ⟨⟨p,D,W,hW,hWD₁,hWD₂,(fun x hx => ((hWV x).mp hx).1),G₁,G₂,eCap,
    hCon₂,hCon₁,hI₂,hI₁,hIso,O₁,O₂,patch,hP,hPn,hPg,hT,hSeam,C⟩⟩

end CalderonPatch
