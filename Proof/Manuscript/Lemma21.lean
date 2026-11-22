module

public import Proof.CalderonPatch.MeasuredBoundaryJets
public import Proof.CalderonPatch.PairedNativeBoundaryBox

import Proof.CalderonPatch.CauchyNormalJets
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

public section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology
open CalderonN (I X axis chartDerivativeWord chartDerivativeWord_ofFn)
open CalderonPatch

namespace CalderonPaper

private theorem chartWord_eq_iterated_of_contDiffOn
    {n : ℕ} (w : List (I n)) {U : Set (X n)} (hU : IsOpen U)
    {f : X n → ℝ} (hf : ContDiffOn ℝ ∞ f U) {x : X n} (hx : x ∈ U) :
    chartDerivativeWord w f x = iteratedFDeriv ℝ w.length f x (fun j => axis (w.get j)) := by
  obtain ⟨f', hf', _, V, hV, hxV, _, hVeq⟩ :=
    CalderonN.exists_contDiff_extension_near_compact hU isCompact_singleton
      (singleton_subset_iff.mpr hx) hf
  have hNear : f' =ᶠ[𝓝 x] f :=
    Filter.mem_of_superset (hV.mem_nhds (hxV (mem_singleton x))) hVeq
  have hEq := congrFun (chartDerivativeWord_ofFn w.length w.get hf') x
  rw [List.ofFn_get] at hEq
  exact (chartDerivativeWord_congr_germ w hNear).eq_of_nhds.symm.trans
    (hEq.trans (congrArg (fun D => D (fun j => axis (w.get j)))
      (hNear.iteratedFDeriv ℝ w.length).eq_of_nhds))

/-- Lemma 2.1 of the September 24, 2026 manuscript. A paired box
represents the two normal coordinate systems with the same tangential
coordinates at the boundary. A derivative word specifies an arbitrary
coordinate partial derivative, including mixed derivatives. -/
theorem lemma21 {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (d₁ d₂ : DirichletData m M)
    {Γ : Set ((𝓡∂ (m+1)).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (p : (𝓡∂ (m+1)).boundary M) (hp : p ∈ Γ)
    (B : PairedNativeBoundaryBox d₁.metric d₂.metric Γ p) :
    ∀ (w : List (I (m+1))) (i j : I (m+1)),
      EqOn
        (fun y => chartDerivativeWord w (fun z => B.first.field z i j) (normalFacePoint y))
        (fun y => chartDerivativeWord w (fun z => B.second.field z i j) (normalFacePoint y))
        (tangentialBox B.boxLower B.boxUpper) := by
  have hm : 2 ≤ m := by omega
  let U : Set (X m) := normalFacePoint ⁻¹' B.signed
  have hU : IsOpen U := B.open_signed.preimage continuous_normalFacePoint
  have hf₁ : MapsTo normalFacePoint U B.first.ambient := fun _ hy => B.signed₁ hy
  have hf₂ : MapsTo normalFacePoint U B.second.ambient := fun _ hy => B.signed₂ hy
  have hQU : MapsTo (WithLp.toLp 2)
      (Icc (B.boxLower ∘ Fin.succAbove 0) (B.boxUpper ∘ Fin.succAbove 0)) U := by
    intro z hz
    have hZ : WithLp.ofLp (normalFacePoint (WithLp.toLp 2 z)) ∈ Icc B.boxLower B.boxUpper :=
      normalFacePoint_in_closedBox B.lower_zero B.upper_pos.le hz
    have h := B.closed_box hZ
    rw [WithLp.toLp_ofLp] at h
    exact h
  let η : ContDiffBump (0 : ℝ) := ⟨B.boxUpper 0 / 4, B.boxUpper 0 / 2,
    by linarith only [B.upper_pos], by linarith only [B.upper_pos]⟩
  have hη : η.rOut < B.boxUpper 0 := by
    change B.boxUpper 0 / 2 < B.boxUpper 0
    linarith only [B.upper_pos]
  have hNormal := BoundaryLayer.normalMetricJets_eqOn_of_patchEnergy B.first B.second hm
    hEnergy B.bounds B.lower_zero B.open_signed B.signed₁ B.signed₂ B.closed_box B.common_inverse
    B.face_patch hU hf₁ hf₂ hQU η hη
  let V := B.signed ∩ normalTangentialCoordinates ⁻¹' tangentialBox B.boxLower B.boxUpper
  have hV : IsOpen V := B.open_signed.inter ((isOpen_tangentialBox _ _).preimage
    contDiff_normalTangentialCoordinates.continuous)
  intro w i j
  let f₁ := fun z => B.first.field z i j
  let f₂ := fun z => B.second.field z i j
  have hs₁ : ContDiffOn ℝ ∞ f₁ V := (B.first.smooth_field.1 i j).mono
    (inter_subset_left.trans B.signed₁)
  have hs₂ : ContDiffOn ℝ ∞ f₂ V := (B.second.smooth_field.1 i j).mono
    (inter_subset_left.trans B.signed₂)
  have hNormal' (k : ℕ) : EqOn (chartDerivativeWord (List.replicate k 0) f₁)
      (chartDerivativeWord (List.replicate k 0) f₂) (boundaryFace V 0) := by
    intro z hz
    let y := normalTangentialCoordinates z
    have hy : y ∈ tangentialBox B.boxLower B.boxUpper := hz.1.2
    have hFace : normalFacePoint y = z := normalFacePoint_tangentialCoordinates hz.2
    have h := hNormal k i j hy
    change BoundaryLayer.normalJetAt f₁ k y = BoundaryLayer.normalJetAt f₂ k y at h
    rw [BoundaryLayer.normalJetAt_eq_chartDerivativeWord B.first.open_ambient
        (B.first.smooth_field.1 i j) (hFace.symm ▸ B.signed₁ hz.1.1),
      BoundaryLayer.normalJetAt_eq_chartDerivativeWord B.second.open_ambient
        (B.second.smooth_field.1 i j) (hFace.symm ▸ B.signed₂ hz.1.1), hFace] at h
    exact h
  intro y hy
  have hyI : WithLp.ofLp y ∈
      Icc (B.boxLower ∘ Fin.succAbove 0) (B.boxUpper ∘ Fin.succAbove 0) :=
    ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩
  have hyU : y ∈ U := by simpa only [WithLp.toLp_ofLp] using hQU hyI
  have hYV : normalFacePoint y ∈ V := by
    refine ⟨hyU, ?_⟩
    change normalTangentialCoordinates (normalFacePoint y) ∈ tangentialBox B.boxLower B.boxUpper
    simpa only [normalTangentialCoordinates_facePoint] using hy
  have hY : normalFacePoint y ∈ boundaryFace V 0 := ⟨hYV, normalFacePoint_height y⟩
  change chartDerivativeWord w f₁ (normalFacePoint y) =
    chartDerivativeWord w f₂ (normalFacePoint y)
  rw [chartWord_eq_iterated_of_contDiffOn w hV hs₁ hYV,
    chartWord_eq_iterated_of_contDiffOn w hV hs₂ hYV,
    iteratedFDeriv_eqOn_of_pure_normal_jets_local hV hs₁ hs₂ hNormal' w.length hY]


end CalderonPaper
