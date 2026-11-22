module

public import Proof.CalderonPatch.NativeBoundaryGreen

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Filter Function Metric Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X)

variable {m : ℕ}

local notation "N" => (m + 1)
local notation "J" => 𝓡∂ N
local notation "R" => 𝓘(ℝ, ℝ)
local notation "H" => inwardHalfSpace N

/-- The tangential coordinates on a boundary normal chart. -/
def normalTangentialCoordinates (x : X N) : X m :=
  WithLp.toLp 2 fun i => x ((0 : I N).succAbove i)

/-- The flat-face point at height zero, given its tangential coordinates. -/
def normalFacePoint (z : X m) : X N :=
  WithLp.toLp 2 (Fin.insertNth (0 : I N) 0 (fun i => z i))

theorem normalFacePoint_height (z : X m) : normalFacePoint z 0 = 0 := by
  change Fin.insertNth (α := fun _ : I N => ℝ) 0 0 (fun i => z i) 0 = 0
  exact Fin.insertNth_apply_same _ _ _

theorem normalTangentialCoordinates_facePoint (z : X m) :
    normalTangentialCoordinates (normalFacePoint z) = z := by
  apply WithLp.ofLp_injective
  funext i
  change Fin.insertNth (α := fun _ : I N => ℝ) 0 0 (fun j => z j) ((0 : I N).succAbove i) = z i
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem contDiff_normalTangentialCoordinates : ContDiff ℝ ∞ (normalTangentialCoordinates (m := m)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I m => ℝ)).symm.contDiff.comp
    (contDiff_pi.mpr fun i => (EuclideanSpace.proj (𝕜 := ℝ) ((0 : I N).succAbove i)).contDiff)

theorem continuous_normalFacePoint : Continuous (normalFacePoint (m := m)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : I N => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [Fin.insertNth_apply_same] using (continuous_const : Continuous (fun _ : X m => (0 : ℝ)))
  · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [Fin.insertNth_apply_succAbove]
    change Continuous (EuclideanSpace.proj (𝕜 := ℝ) j : X m → ℝ)
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous

/-- The open bottom face of a coordinate half box in its tangential variables. -/
def tangentialBox (a b : I N → ℝ) : Set (X m) :=
  {z | ∀ i : I m, a ((0 : I N).succAbove i) < z i ∧ z i < b ((0 : I N).succAbove i)}

theorem isOpen_tangentialBox (a b : I N → ℝ) : IsOpen (tangentialBox a b) := by
  let Q : Set (I m → ℝ) := univ.pi fun i => Ioo (a ((0 : I N).succAbove i)) (b ((0 : I N).succAbove i))
  have hQ : IsOpen Q := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hq : tangentialBox a b = WithLp.ofLp ⁻¹' Q := by
    ext z
    simp [tangentialBox,Q,Set.mem_pi]
  rw [hq]
  exact hQ.preimage (PiLp.continuous_ofLp 2 (fun _ : I m => ℝ))

/-- A smooth compactly supported tangential test extends with the same
trace and is supported away from the other faces of the half box. -/
theorem exists_halfBoxTest {a b : I N → ℝ} (hb : 0 < b 0)
    {φ : X m → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ tangentialBox a b) :
    ∃ f : X N → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ∩ H ⊆ normalHalfBox a b ∧ f ∘ normalFacePoint = φ := by
  let χ : ContDiffBump (0 : ℝ) := ⟨b 0 / 4,b 0 / 2,by positivity,by linarith⟩
  let P := normalTangentialCoordinates (m := m)
  let t := EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)
  let f := fun x : X N => χ (t x) * φ (P x)
  have hf : ContDiff ℝ ∞ f := (χ.contDiff.comp t.contDiff).mul
    (hφ.comp contDiff_normalTangentialCoordinates)
  let A := tsupport (χ : ℝ → ℝ)
  let B := tsupport φ
  let K : Set (X N) := t ⁻¹' A ∩ P ⁻¹' B
  have hkClosed : IsClosed K := ((isClosed_tsupport (χ : ℝ → ℝ)).preimage t.continuous).inter
    ((isClosed_tsupport φ).preimage contDiff_normalTangentialCoordinates.continuous)
  have hSub : tsupport f ⊆ K := by
    apply closure_minimal _ hkClosed
    intro x hx
    have hn : χ (t x) * φ (P x) ≠ 0 := hx
    exact ⟨subset_closure (show χ (t x) ≠ 0 from (mul_ne_zero_iff.mp hn).1),
      subset_closure (show φ (P x) ≠ 0 from (mul_ne_zero_iff.mp hn).2)⟩
  let F (q : ℝ × X m) : X N := WithLp.toLp 2 (Fin.insertNth (0 : I N) q.1 (fun i => q.2 i))
  have hF : Continuous F := by
    apply (PiLp.continuous_toLp 2 (fun _ : I N => ℝ)).comp
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · subst i
      simpa only [Fin.insertNth_apply_same] using (continuous_fst : Continuous (fun q : ℝ × X m => q.1))
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
      simp only [Fin.insertNth_apply_succAbove]
      change Continuous ((EuclideanSpace.proj (𝕜 := ℝ) j : X m → ℝ) ∘ Prod.snd : ℝ × X m → ℝ)
      exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp continuous_snd
  have hK : IsCompact K := by
    apply ((χ.hasCompactSupport.prod hφc).image hF).of_isClosed_subset hkClosed
    intro x hx
    refine ⟨(t x,P x),hx,?_⟩
    apply WithLp.ofLp_injective
    change Fin.insertNth (α := fun _ : I N => ℝ) 0 (x 0)
      (Fin.removeNth 0 (fun i => x i)) = WithLp.ofLp x
    simpa only [Function.update_eq_self] using Fin.insertNth_removeNth 0 (x 0) (fun i => x i)
  refine ⟨f,hf,hK.of_isClosed_subset (isClosed_tsupport f) hSub,?_,?_⟩
  · intro x hx
    have hxK := hSub hx.1
    have ht : t x ∈ closedBall (0 : ℝ) (b 0 / 2) := by
      have h := hxK.1
      change t x ∈ tsupport (χ : ℝ → ℝ) at h
      rwa [χ.tsupport_eq] at h
    have htUpper : x 0 < b 0 := by
      have h := Metric.mem_closedBall.mp ht
      rw [Real.dist_eq, sub_zero] at h
      have h' := (le_abs_self (t x)).trans h
      change x 0 ≤ b 0 / 2 at h'
      linarith
    have hTangential := hφs hxK.2
    have hxP (i : I m) : a ((0 : I N).succAbove i) < x ((0 : I N).succAbove i) ∧
        x ((0 : I N).succAbove i) < b ((0 : I N).succAbove i) := hTangential i
    refine ⟨hx.2,?_,?_⟩
    · intro i
      by_cases hi : i = 0
      · simpa only [hi] using htUpper
      · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
        exact (hxP j).2
    · intro i hi
      obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hi
      exact (hxP j).1
  · funext x
    have hχ0 : χ 0 = 1 := χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)
    change χ (normalFacePoint x 0) * φ (normalTangentialCoordinates (normalFacePoint x)) = φ x
    rw [normalFacePoint_height, normalTangentialCoordinates_facePoint, hχ0, one_mul]

theorem normalHalfBox_subset_closedBox {a b : I N → ℝ} (ha : a 0 = 0) :
    normalHalfBox a b ⊆ WithLp.ofLp ⁻¹' Icc a b := by
  intro x hx
  refine ⟨?_,fun i => (hx.2.1 i).le⟩
  intro i
  by_cases hi : i = 0
  · subst i
    rw [ha]
    exact hx.1
  · exact (hx.2.2 i hi).le

theorem normalFacePoint_in_closedBox {a b : I N → ℝ} (hBottom : a 0 = 0) (hb : 0 ≤ b 0)
    {z : X m} (hz : WithLp.ofLp z ∈ Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)) :
    WithLp.ofLp (normalFacePoint z) ∈ Icc a b :=
  insertNth_mem_box 0 ⟨hBottom.le,hb⟩ hz

theorem normalFacePoint_tangentialCoordinates {x : X N} (hx : x 0 = 0) :
    normalFacePoint (normalTangentialCoordinates x) = x := by
  apply WithLp.ofLp_injective
  change Fin.insertNth (α := fun _ : I N => ℝ) 0 0 (Fin.removeNth 0 (fun i => x i)) = WithLp.ofLp x
  have h := Fin.insertNth_removeNth 0 (x 0) (WithLp.ofLp x)
  rw [Function.update_eq_self] at h
  rwa [hx] at h

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]

/-- Extension by zero of a relative chart function, across the part
of the manifold outside the normal chart. -/
def boundaryChartTest {g : SmoothMetric N M} {p : M} (D : NativeBoundaryMetricChart g p)
    (f : X N → ℝ) : M → ℝ := D.coord.source.indicator (f ∘ D.coord)

theorem tsupport_boundaryChartTest_subset {g : SmoothMetric N M} {p : M}
    (D : NativeBoundaryMetricChart g p) {f : X N → ℝ} (hf : HasCompactSupport f)
    (hS : tsupport f ∩ H ⊆ D.coord.target) :
    tsupport (boundaryChartTest D f) ⊆ D.coord.symm '' (tsupport f ∩ H) := by
  have hC : IsCompact (tsupport f ∩ H) :=
    hf.inter_right (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)).continuous)
  apply closure_minimal _ (hC.image_of_continuousOn (D.smooth_inverse.continuousOn.mono hS)).isClosed
  intro x hx
  by_cases hxe : x ∈ D.coord.source
  · have hn : f (D.coord x) ≠ 0 := by
      change boundaryChartTest D f x ≠ 0 at hx
      rwa [boundaryChartTest, indicator_of_mem hxe] at hx
    have hH : D.coord x ∈ H := (D.target_eq ▸ D.coord.map_source hxe : _ ∈ D.ambient ∩ H).2
    exact ⟨D.coord x, ⟨subset_closure hn,hH⟩, D.coord.left_inv hxe⟩
  · apply (hx : boundaryChartTest D f x ≠ 0).elim
    rw [boundaryChartTest, indicator_of_notMem hxe]

theorem contMDiff_boundaryChartTest {g : SmoothMetric N M} {p : M}
    (D : NativeBoundaryMetricChart g p) {f : X N → ℝ} (hf : ContDiff ℝ ∞ f)
    (hC : HasCompactSupport f) (hS : tsupport f ∩ H ⊆ D.coord.target) :
    ContMDiff J R ∞ (boundaryChartTest D f) := by
  intro x
  by_cases hx : x ∈ D.coord.source
  · have hD := hf.contMDiff.comp_contMDiffOn D.smooth
    apply (hD.contMDiffAt (D.open_source.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [D.open_source.mem_nhds hx] with y hy
    rw [boundaryChartTest, indicator_of_mem hy]
  · have hNot : x ∉ tsupport (boundaryChartTest D f) := by
      intro h
      obtain ⟨z,hz,rfl⟩ := tsupport_boundaryChartTest_subset D hC hS h
      exact hx (D.coord.map_target (hS hz))
    exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hNot)

omit [T2Space M] in
theorem boundaryChartTest_comp_inverse {g : SmoothMetric N M} {p : M}
    (D : NativeBoundaryMetricChart g p) (f : X N → ℝ) :
    EqOn (boundaryChartTest D f ∘ D.coord.symm) f D.coord.target := by
  intro x hx
  rw [Function.comp_apply,boundaryChartTest, indicator_of_mem (D.coord.map_target hx),
    Function.comp_apply, D.coord.right_inv hx]

/-- The intrinsic support of the native test stays inside the
selected coordinate half box. -/
theorem tsupport_boundaryChartTest_subset_halfBox {g : SmoothMetric N M} {p : M}
    (D : NativeBoundaryMetricChart g p) {a b : I N → ℝ} (hBottom : a 0 = 0)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) D.ambient)
    {f : X N → ℝ} (hf : HasCompactSupport f) (hSupp : tsupport f ∩ H ⊆ normalHalfBox a b) :
    tsupport (boundaryChartTest D f) ⊆ D.coord.source ∩ D.coord ⁻¹' normalHalfBox a b := by
  have hT : tsupport f ∩ H ⊆ D.coord.target := by
    intro x hx
    have h := hBox (normalHalfBox_subset_closedBox hBottom (hSupp hx))
    change WithLp.toLp 2 (WithLp.ofLp x) ∈ D.ambient at h
    rw [WithLp.toLp_ofLp] at h
    exact D.target_eq.symm ▸ ⟨h,hx.2⟩
  intro x hx
  obtain ⟨z,hz,rfl⟩ := tsupport_boundaryChartTest_subset D hf hT hx
  refine ⟨D.coord.map_target (hT hz),?_⟩
  change D.coord (D.coord.symm z) ∈ normalHalfBox a b
  rw [D.coord.right_inv (hT hz)]
  exact hSupp hz

omit [T2Space M] in
/-- Boundary points in a native normal chart have height zero. -/
theorem NativeBoundaryMetricChart.coord_height_eq_zero {g : SmoothMetric N M} {p q : M}
    (D : NativeBoundaryMetricChart g p) (hq : q ∈ D.coord.source)
    (hBd : q ∈ (J).boundary M) : D.coord q 0 = 0 := by
  have hT := D.coord.map_source hq
  have hnonneg := (mem_inwardHalfSpace.mp (D.target_eq ▸ hT : _ ∈ D.ambient ∩ H).2)
  apply le_antisymm _ hnonneg
  apply le_of_not_gt
  intro h
  have hb : q ∈ ((J).interior M)ᶜ := by rw [(J).compl_interior]; exact hBd
  exact hb ((D.interior_iff q hq).mpr (mem_positiveHalfSpace.mpr h))

/-- Two chart tests defined using the same signed function and matching
boundary parametrizations have the same trace on the original boundary. -/
theorem eqOn_boundaryChartTests_of_paired_coordinates
    {g₁ g₂ : SmoothMetric N M} {p₁ p₂ : M}
    (D₁ : NativeBoundaryMetricChart g₁ p₁) (D₂ : NativeBoundaryMetricChart g₂ p₂)
    {f : X N → ℝ} (hf : HasCompactSupport f)
    (h₁ : tsupport f ∩ H ⊆ D₁.coord.target) (h₂ : tsupport f ∩ H ⊆ D₂.coord.target)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (tsupport f ∩ {x | x 0 = 0})) :
    EqOn (boundaryChartTest D₁ f) (boundaryChartTest D₂ f) ((J).boundary M) := by
  have hAux (z : X N) (hz : z ∈ tsupport f ∩ H) :
      boundaryChartTest D₁ f (D₁.coord.symm z) = boundaryChartTest D₂ f (D₂.coord.symm z) :=
    (boundaryChartTest_comp_inverse D₁ f (h₁ hz)).trans
      (boundaryChartTest_comp_inverse D₂ f (h₂ hz)).symm
  intro x hx
  by_cases h₁x : x ∈ tsupport (boundaryChartTest D₁ f)
  · obtain ⟨z,hz,rfl⟩ := tsupport_boundaryChartTest_subset D₁ hf h₁ h₁x
    have hNormal := D₁.coord_height_eq_zero (D₁.coord.map_target (h₁ hz)) hx
    rw [D₁.coord.right_inv (h₁ hz)] at hNormal
    exact (hAux z hz).trans (congrArg (boundaryChartTest D₂ f) (hSame ⟨hz.1,hNormal⟩)).symm
  · by_cases h₂x : x ∈ tsupport (boundaryChartTest D₂ f)
    · obtain ⟨z,hz,rfl⟩ := tsupport_boundaryChartTest_subset D₂ hf h₂ h₂x
      have hNormal := D₂.coord_height_eq_zero (D₂.coord.map_target (h₂ hz)) hx
      rw [D₂.coord.right_inv (h₂ hz)] at hNormal
      exact (congrArg (boundaryChartTest D₁ f) (hSame ⟨hz.1,hNormal⟩)).symm.trans (hAux z hz)
    · exact (image_eq_zero_of_notMem_tsupport h₁x).trans (image_eq_zero_of_notMem_tsupport h₂x).symm

end CalderonPatch
