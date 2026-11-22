module

public import Proof.CalderonPatch.CapGreenAgreement
public import Proof.CalderonPatch.FrontierFromSources
public import Proof.CalderonPatch.InteriorContinuation
public import Proof.CalderonPatch.SeedIsometry
public import Proof.CalderonPatch.SourceDifferentials

import Proof.CalderonN.GreenRestriction

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (I X Mat IsDirichletGreenKernel HarmonicCoordinates hessian)

variable {n : ℕ} [NeZero n] {F M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

/-- Shared cap coordinates and representation of the same test source by
the same evaluation label on both extended manifolds. -/
structure CommonCapSources (E₂ : SourceEvaluations M₂ F) (E₁ : SourceEvaluations M₁ F)
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    (Seed : EvaluationMatch E₂ E₁ (IsLocalMetricIsometry g₁ g₂))
    (G₁ : M₁ × M₁ → ℝ) (G₂ : M₂ × M₂ → ℝ) where
  first : OpenPartialHomeomorph M₁ (X n)
  second : OpenPartialHomeomorph M₂ (X n)
  domain : Set (X n)
  open_domain : IsOpen domain
  connected_domain : IsConnected domain
  first_target : domain ⊆ first.target
  second_target : domain ⊆ second.target
  source_closure : closure (second.symm '' domain) ⊆ Seed.chart.source
  same_coordinates : EqOn first.symm (Seed.chart ∘ second.symm) domain
  density : X n → ℝ
  density_continuous : ContinuousOn density domain
  density_pos : ∀ x ∈ domain, 0 < density x
  representation : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ domain →
    ∃ b : F,
      (∀ p ∈ (𝓡∂ n).interior M₁, E₁.value p b = ∫ x in domain, φ x * G₁ (first.symm x, p) * density x) ∧
      (∀ p ∈ (𝓡∂ n).interior M₂, E₂.value p b = ∫ x in domain, φ x * G₂ (second.symm x, p) * density x)

variable [CompactSpace M₁] [CompactSpace M₂] [LocallyConnectedSpace M₂]

/-- The no-interior-frontier proposition from the actual extended source
families. The cap construction and source jet realization supply its
inputs. Every frontier uses the same source labels and the true kernels
when applying the checked local extension theorem. -/
theorem exists_globalInteriorIsometry_of_cap_sources (hn : 3 ≤ n)
    (E₂ : SourceEvaluations M₂ F) (E₁ : SourceEvaluations M₁ F)
    (hI₂ : E₂.interior = (𝓡∂ n).interior M₂) (hI₁ : E₁.interior = (𝓡∂ n).interior M₁)
    (hConn₂ : IsConnected E₂.interior) (hConn₁ : IsConnected E₁.interior)
    (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂} (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel J μ₁ (nativeLaplace g₁) G₁)
    (hG₂ : IsDirichletGreenKernel J μ₂ (nativeLaplace g₂) G₂)
    (Seed : EvaluationMatch E₂ E₁ (IsLocalMetricIsometry g₁ g₂))
    (hSeedConn : IsPreconnected Seed.chart.source) {s : M₂} (hs : s ∈ Seed.chart.source)
    (C : CommonCapSources E₂ E₁ Seed G₁ G₂)
    (hSmooth₁ : ∀ b, ContMDiff J R ∞ (fun x => E₁.value x b))
    (hSmooth₂ : ∀ b, ContMDiff J R ∞ (fun x => E₂.value x b))
    (hH₁ : ∀ b, EqOn (nativeLaplace g₁ (fun x => E₁.value x b)) 0
      ((𝓡∂ n).interior M₁ \ (Seed.chart '' closure (C.second.symm '' C.domain))))
    (hH₂ : ∀ b, EqOn (nativeLaplace g₂ (fun x => E₂.value x b)) 0
      ((𝓡∂ n).interior M₂ \ closure (C.second.symm '' C.domain)))
    (hJets₂ : ∀ p ∈ (𝓡∂ n).interior M₂ \ closure (C.second.symm '' C.domain),
      ∀ A : TangentSpace J p →L[ℝ] ℝ, ∃ b, mfderiv J R (fun x => E₂.value x b) p = A)
    (hJets₁ : ∀ e : OpenPartialHomeomorph M₁ (X n),
      e.source ⊆ (𝓡∂ n).interior M₁ \ (Seed.chart '' closure (C.second.symm '' C.domain)) →
      ContMDiffOn J K ∞ e e.source → ContMDiffOn K J ∞ e.symm e.target →
      HarmonicCoordinates e.target (coordinateMetric g₁ e) →
      ∀ x ∈ e.target, ∀ A : Mat n,
        A ∈ Submodule.span ℝ (range fun b => hessian (fun z => E₁.value (e.symm z) b) x) ↔
          A.transpose = A ∧ ((coordinateMetric g₁ e x)⁻¹ * A).trace = 0) :
    ∃ e : OpenPartialHomeomorph M₂ M₁,
      e.source = E₂.interior ∧ e.target = E₁.interior ∧ IsLocalMetricIsometry g₁ g₂ e ∧
      (∀ p ∈ e.source, E₂.value p = E₁.value (e p)) ∧
      ∀ T : EvaluationMatch E₂ E₁ (IsLocalMetricIsometry g₁ g₂), EqOn e T.chart T.chart.source := by
  let D := matchingDomain E₂ E₁ (IsLocalMetricIsometry g₁ g₂)
  let W := connectedComponentIn D s
  let S₂ := closure (C.second.symm '' C.domain)
  let S₁ := Seed.chart '' S₂
  let U₂ := (𝓡∂ n).interior M₂ \ S₂
  let U₁ := (𝓡∂ n).interior M₁ \ S₁
  have hsd := Seed.source_subset_matchingDomain hs
  have hSeedW : Seed.chart.source ⊆ W :=
    hSeedConn.subset_connectedComponentIn hs Seed.source_subset_matchingDomain
  have hS₂W : S₂ ⊆ W := C.source_closure.trans hSeedW
  have hS₁ : IsClosed S₁ := (isClosed_closure.isCompact.image_of_continuousOn
    (Seed.chart.continuousOn.mono C.source_closure)).isClosed
  have hU₁ : IsOpen U₁ := ((𝓡∂ n).isOpen_interior (n := ∞) (by simp)).sdiff hS₁
  have hU₂ : IsOpen U₂ := ((𝓡∂ n).isOpen_interior (n := ∞) (by simp)).sdiff isClosed_closure
  obtain ⟨Φ, hΦsrc, hΦtar, hΦ, hEval, hAgree⟩ := exists_seedComponent_isometry E₂ E₁ g₁ g₂ Seed s
  have hΦc : IsConnected Φ.source := by
    rw [hΦsrc]
    exact isConnected_connectedComponentIn_iff.mpr hsd
  have hΦI₂ : Φ.source ⊆ (𝓡∂ n).interior M₂ := by
    rw [hΦsrc, ← hI₂]
    exact (connectedComponentIn_subset D s).trans (matchingDomain_subset_interior E₂ E₁ _)
  have hΦI₁ : Φ.target ⊆ (𝓡∂ n).interior M₁ := hΦtar.trans (le_of_eq hI₁)
  have hΦEval : ∀ x ∈ Φ.source, E₂.value x = E₁.value (Φ x) := fun x hx => hEval x (hΦsrc ▸ hx)
  have hCap : MapsTo C.second.symm C.domain Φ.source := by
    intro x hx
    rw [hΦsrc]
    exact hS₂W (subset_closure (mem_image_of_mem C.second.symm hx))
  have hCapEq : EqOn C.first.symm (Φ ∘ C.second.symm) C.domain := by
    intro x hx
    exact (C.same_coordinates hx).trans (hAgree Seed (C.source_closure
      (subset_closure (mem_image_of_mem C.second.symm hx)))).symm
  have hGreen := green_eqOn_of_capSourceRepresentations (show 2 ≤ n from by omega)
    Φ hΦ hΦI₂ hΦI₁ hΦc hμ₁ hμ₂ hG₁ hG₂ C.first C.second C.open_domain C.connected_domain
    C.first_target C.second_target hCap hCapEq E₁.value E₂.value hΦEval C.density
    C.density_continuous C.density_pos C.representation
  apply exists_globalInteriorIsometry hn E₂ E₁ hI₁ hI₂ hConn₁ hConn₂ g₁ g₂
    (fun f _ => tsupport_nativeLaplace_subset g₁ f) (fun f _ => tsupport_nativeLaplace_subset g₂ f)
    hG₁ hG₂ hsd
  change ∀ p ∈ E₂.interior, p ∈ closure W → p ∉ W →
    Nonempty (FrontierCharts E₂ E₁ g₁ g₂ μ₁ μ₂ (nativeLaplace g₁) (nativeLaplace g₂) G₁ G₂ W p)
  intro p hp hpcl hpW
  have hpI : p ∈ (𝓡∂ n).interior M₂ := hI₂ ▸ hp
  obtain ⟨q, hq, hqUnique⟩ := existsUnique_partner_of_mem_closure E₂ E₁ hp hpcl
    (fun x hx => ⟨Φ x, hEval x hx⟩)
  have hqI : q ∈ (𝓡∂ n).interior M₁ := hI₁ ▸ interior_of_equal_evaluations E₂ E₁ hp hq
  have hpU : p ∈ U₂ := ⟨hpI, fun h => hpW (hS₂W h)⟩
  have hqU : q ∈ U₁ := by
    refine ⟨hqI, ?_⟩
    rintro ⟨x, hx, rfl⟩
    have hxS := C.source_closure hx
    have hpx := E₂.separates hp (Seed.source_interior hxS) (hq.trans (Seed.evaluation_eq x hxS).symm)
    exact hpU.2 (hpx.symm ▸ hx)
  have hpcl' : p ∈ closure Φ.source := hΦsrc.symm ▸ hpcl
  have hlim : Tendsto Φ (𝓝[Φ.source] p) (𝓝 q) := by
    intro V hV
    change ∀ᶠ x in 𝓝[Φ.source] p, Φ x ∈ V
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [eventually_partners_mem E₂ E₁ hV hqUnique] with x hx hxΦ
    exact hx (Φ x) (hΦEval x hxΦ)
  obtain ⟨a, hD₂⟩ := exists_invertible_tuple_of_realized_covectors E₂.value hSmooth₂ p (hJets₂ p hpU)
  have hf₁ := contMDiff_sourceTuple E₁.value a hSmooth₁
  have hf₂ := contMDiff_sourceTuple E₂.value a hSmooth₂
  have hfEq : EqOn (sourceTuple E₂.value a) (sourceTuple E₁.value a ∘ Φ) Φ.source := by
    intro x hx
    unfold sourceTuple
    simp only [Function.comp_apply, hΦEval x hx]
  have hvEq : sourceTuple E₂.value a p = sourceTuple E₁.value a q := by
    unfold sourceTuple
    simp only [hq]
  have hD₁ := invertible_mfderiv_at_partner hΦ hpI hqI hpcl' hlim hf₁ hf₂ hfEq hD₂
  obtain ⟨P⟩ := exists_paired_sourceCharts hU₁ hU₂ hqI hpI hqU hpU hf₁ hf₂ hD₁ hD₂ hvEq hfEq hlim
  have hpt : P.second p ∈ P.first.target := P.target_eq.symm ▸ P.second.map_source P.second_center
  have hCharts := frontierCharts_of_harmonic_sources hμ₁ hμ₂ hΦ P hSmooth₁ hSmooth₂ hH₁ hH₂ hΦEval hGreen
    (fun hc => hJets₁ P.first P.first_domain P.first_smooth P.first_inverse_smooth hc _ hpt)
  change Φ.source = W at hΦsrc
  rw [← hΦsrc]
  exact hCharts

end CalderonPatch
