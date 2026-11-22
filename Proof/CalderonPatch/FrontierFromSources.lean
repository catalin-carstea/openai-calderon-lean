module

public import Proof.CalderonPatch.FrontierCharts
public import Proof.CalderonPatch.HessianRank
public import Proof.CalderonPatch.IsometricCharts
public import Proof.CalderonPatch.PairedSourceCharts

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Proof.CalderonN.GreenWeak

@[expose] public section

noncomputable section
open Metric Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X Mat Harmonic HarmonicCoordinates hessian laplace_congrOn)

variable {n : ℕ} [NeZero n] {F : Type*}

omit [NeZero n] in
/-- A family spanning the full harmonic Hessian hyperplane contains
a finite list of source labels whose Hessians form a basis. -/
theorem exists_hessian_basis {γ : CalderonN.MetricField n} {u : F → X n → ℝ} {z : X n}
    (hspan : ∀ H : Mat n, H ∈ Submodule.span ℝ (range fun a => hessian (u a) z) ↔
      H.transpose = H ∧ ((γ z)⁻¹ * H).trace = 0) :
    ∃ (k : ℕ) (a : Fin k → F),
      LinearIndependent ℝ (fun i => hessian (u (a i)) z) ∧
      HessianSpanningAt γ (fun i => u (a i)) z := by
  classical
  let H : F → Mat n := fun a => hessian (u a) z
  obtain ⟨ι, a, _, hsp, hLI⟩ := exists_linearIndependent' (K := ℝ) H
  let _ : Finite ι := hLI.finite
  let _ : Fintype ι := Fintype.ofFinite ι
  let d := Fintype.equivFin ι
  refine ⟨Fintype.card ι, a ∘ d.symm, hLI.comp d.symm d.symm.injective, ?_⟩
  intro A
  have hRange : range (H ∘ (a ∘ d.symm)) = range (H ∘ a) :=
    d.symm.surjective.range_comp (H ∘ a)
  change A ∈ Submodule.span ℝ (range (H ∘ (a ∘ d.symm))) ↔ _
  rw [hRange, hsp]
  exact hspan A

section HarmonicCoordinate

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

theorem harmonic_in_nativeChart (g : SmoothMetric n M)
    (e : OpenPartialHomeomorph M (X n)) (hI : e.source ⊆ (𝓡∂ n).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source)
    (hΔ : EqOn (nativeLaplace g u) 0 e.source) :
    Harmonic e.target (coordinateMetric g e) (u ∘ e.symm) := by
  refine ⟨(hu.comp hes e.symm.mapsTo).contDiffOn, ?_⟩
  intro x hx
  have h := nativeLaplace_eq_coordinate g e hI he hes hu (e.map_target hx)
  rw [e.right_inv hx] at h
  exact h.symm.trans (hΔ (e.map_target hx))

theorem harmonicCoordinates_of_sourceTuple (g : SmoothMetric n M)
    (e : OpenPartialHomeomorph M (X n)) (E : M → F → ℝ) (a : I n → F)
    (hE : EqOn e (sourceTuple E a) e.source)
    (hu : ∀ b, Harmonic e.target (coordinateMetric g e) (fun x => E (e.symm x) b)) :
    HarmonicCoordinates e.target (coordinateMetric g e) := by
  intro i
  have hEq : EqOn (fun x => x i) (fun x => E (e.symm x) (a i)) e.target := by
    intro x hx
    have h := congrArg (fun y : X n => y i) (hE (e.map_target hx))
    rwa [e.right_inv hx, sourceTuple_apply] at h
  exact ⟨(hu (a i)).1.congr hEq, fun x hx =>
    (laplace_congrOn e.open_target (fun _ _ => rfl) hEq hx).trans ((hu (a i)).2 x hx)⟩

end HarmonicCoordinate

section Frontier

variable {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- The paired harmonic chart and its finite Hessian basis produce the
exact input of the touching-ball argument, including both native kernel
restrictions and the evaluations of every source. -/
theorem frontierCharts_of_harmonic_sources
    {E₁ : SourceEvaluations M₁ F} {E₂ : SourceEvaluations M₂ F}
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {μ₁ : MeasureTheory.Measure M₁} {μ₂ : MeasureTheory.Measure M₂}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    {Φ : OpenPartialHomeomorph M₂ M₁} (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    {a : I n → F} {U₁ : Set M₁} {U₂ : Set M₂} {q : M₁} {p : M₂}
    (C : PairedSourceCharts Φ (sourceTuple E₁.value a) (sourceTuple E₂.value a) U₁ U₂ q p)
    (hS₁ : ∀ s, ContMDiff J R ∞ (fun x => E₁.value x s))
    (hS₂ : ∀ s, ContMDiff J R ∞ (fun x => E₂.value x s))
    (hΔ₁ : ∀ s, EqOn (nativeLaplace g₁ (fun x => E₁.value x s)) 0 U₁)
    (hΔ₂ : ∀ s, EqOn (nativeLaplace g₂ (fun x => E₂.value x s)) 0 U₂)
    (hEval : ∀ x ∈ Φ.source, E₂.value x = E₁.value (Φ x))
    (hGreen : ∀ x ∈ Φ.source, ∀ y ∈ Φ.source, y ≠ x → G₁ (Φ y, Φ x) = G₂ (y, x))
    (hspan : HarmonicCoordinates C.first.target (coordinateMetric g₁ C.first) →
      let γ := coordinateMetric g₁ C.first
      let z := C.second p
      ∀ H : Mat n, H ∈ Submodule.span ℝ (range fun s => hessian (fun x => E₁.value (C.first.symm x) s) z) ↔
        H.transpose = H ∧ ((γ z)⁻¹ * H).trace = 0) :
    Nonempty (FrontierCharts E₂ E₁ g₁ g₂ μ₁ μ₂ (nativeLaplace g₁) (nativeLaplace g₂)
      G₁ G₂ Φ.source p) := by
  let γ₁ := coordinateMetric g₁ C.first
  let γ₂ := coordinateMetric g₂ C.second
  let z := C.second p
  have hz₂ : z ∈ C.second.target := C.second.map_source C.second_center
  have hz₁ : z ∈ C.first.target := C.target_eq.symm ▸ hz₂
  have hH₁ s : Harmonic C.first.target γ₁ (fun x => E₁.value (C.first.symm x) s) :=
    harmonic_in_nativeChart g₁ C.first C.first_interior C.first_smooth C.first_inverse_smooth
      (hS₁ s).contMDiffOn ((hΔ₁ s).mono C.first_domain)
  have hH₂ s : Harmonic C.second.target γ₂ (fun x => E₂.value (C.second.symm x) s) :=
    harmonic_in_nativeChart g₂ C.second C.second_interior C.second_smooth C.second_inverse_smooth
      (hS₂ s).contMDiffOn ((hΔ₂ s).mono C.second_domain)
  have hC₁ := harmonicCoordinates_of_sourceTuple g₁ C.first E₁.value a C.first_coordinates hH₁
  have hC₂ := harmonicCoordinates_of_sourceTuple g₂ C.second E₂.value a C.second_coordinates hH₂
  have hg₁ := coordinateMetric_smooth g₁ C.first C.first_smooth C.first_inverse_smooth
  obtain ⟨k, s, hind, hbase⟩ := exists_hessian_basis (hspan hC₁)
  obtain ⟨V, hV, hzV, hV₁, hspans⟩ :=
    exists_harmonic_hessianSpanning_neighborhood C.first.open_target hz₁ hg₁ hC₁
      (fun i => hH₁ (s i)) hind hbase
  obtain ⟨r, hr, hBV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hzV)
  let B := ball z r
  have hB₁ : B ⊆ C.first.target := hBV.trans hV₁
  have hB₂ : B ⊆ C.second.target := C.target_eq ▸ hB₁
  let a₁ := C.first.trans (OpenPartialHomeomorph.ofSet B isOpen_ball)
  let a₂ := C.second.trans (OpenPartialHomeomorph.ofSet B isOpen_ball)
  obtain ⟨ha₁t, ha₁s, ha₁, ha₁i⟩ := restrict_smooth_chart C.first C.first_smooth C.first_inverse_smooth
    isOpen_ball hB₁
  obtain ⟨ha₂t, ha₂s, ha₂, ha₂i⟩ := restrict_smooth_chart C.second C.second_smooth C.second_inverse_smooth
    isOpen_ball hB₂
  change a₁.target = B at ha₁t
  change a₂.target = B at ha₂t
  let C₁ := nativeInteriorMetricChart g₁ μ₁ hμ₁ a₁ (ha₁s.trans C.first_interior) ha₁ ha₁i
  let C₂ := nativeInteriorMetricChart g₂ μ₂ hμ₂ a₂ (ha₂s.trans C.second_interior) ha₂ ha₂i
  let A := matchedImage a₂ Φ.source
  have hA : IsOpen A := a₂.isOpen_image_of_subset_source (Φ.open_source.inter a₂.open_source) inter_subset_right
  have hinv : EqOn a₁.symm (Φ ∘ a₂.symm) A := by
    intro x hx
    have h := mem_matchedImage.mp hx
    exact C.inverse_matches x (hB₂ (ha₂t ▸ h.1)) h.2
  have hEq := coordinateMetric_eq_of_isometry hΦ ha₂i hA
    (fun _ hx => (mem_matchedImage.mp hx).1) (fun _ hx => (mem_matchedImage.mp hx).2) hinv
  have ha₁sub : a₁.target ⊆ C.first.target := ha₁t.symm ▸ hB₁
  have ha₂sub : a₂.target ⊆ C.second.target := ha₂t.symm ▸ hB₂
  refine ⟨{
    first := C₁
    second := C₂
    target_eq := ha₁t.trans ha₂t.symm
    point_in_source := ⟨C.second_center, mem_ball_self hr⟩
    first_realizes := realizesCoordinateMetric g₁ a₁
    second_realizes := realizesCoordinateMetric g₂ a₂
    first_harmonic_coord := fun i => ⟨(hC₁ i).1.mono ha₁sub, fun x hx => (hC₁ i).2 x (ha₁sub hx)⟩
    second_harmonic_coord := fun i => ⟨(hC₂ i).1.mono ha₂sub, fun x hx => (hC₂ i).2 x (ha₂sub hx)⟩
    first_sources := fun i => ⟨(hH₁ i).1.mono ha₁sub, fun x hx => (hH₁ i).2 x (ha₁sub hx)⟩
    second_sources := fun i => ⟨(hH₂ i).1.mono ha₂sub, fun x hx => (hH₂ i).2 x (ha₂sub hx)⟩
    metric_eq := hEq
    green_eq := ?_
    evaluations_eq := ?_
    count := k
    sources := s
    spans := by
      intro x hx
      have hx' : x ∈ B := by
        rw [← ha₁t]
        exact hx
      exact hspans x (hBV hx')
  }⟩
  · intro xy hxy
    have h₁ := mem_matchedImage.mp hxy.1
    have h₂ := mem_matchedImage.mp hxy.2.1
    have hne : a₂.symm xy.1 ≠ a₂.symm xy.2 := fun he => hxy.2.2 (a₂.symm.injOn h₁.1 h₂.1 he)
    change G₁ (a₁.symm xy.1, a₁.symm xy.2) = _
    rw [hinv hxy.1, hinv hxy.2.1]
    exact hGreen _ h₂.2 _ h₁.2 hne
  · intro x hx
    change E₁.value (a₁.symm x) = E₂.value (a₂.symm x)
    exact (congrArg E₁.value (hinv hx)).trans (hEval _ (mem_matchedImage.mp hx).2).symm

end Frontier

end CalderonPatch
