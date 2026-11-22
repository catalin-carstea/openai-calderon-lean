module

public import Proof.CalderonPatch.MatchedCoordinates
public import Proof.CalderonPatch.MaximalMatch

@[expose] public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

section OpenGlue

variable {X Y F : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]

/-- Restrict the glued evaluation match to an open domain contained in
the union of matching charts. -/
theorem exists_evaluationMatch_on_open_subset
    (I₂ : SourceEvaluations X F) (I₁ : SourceEvaluations Y F)
    (admissible : OpenPartialHomeomorph X Y → Prop) (defaultTarget : Y)
    {W : Set X} (hW : IsOpen W) (hWD : W ⊆ matchingDomain I₂ I₁ admissible) :
    ∃ e : OpenPartialHomeomorph X Y,
      e.source = W ∧ e.target ⊆ I₁.interior ∧
      (∀ p ∈ W, I₂.value p = I₁.value (e p)) ∧
      ∀ E : EvaluationMatch I₂ I₁ admissible, EqOn e E.chart E.chart.source := by
  obtain ⟨Φ, hLocal, hMaps, hInj, hEval, hAgree⟩ :=
    exists_evaluationMatchGlue I₂ I₁ admissible defaultTarget
  have hOpen : IsOpenMap (W.domRestrict Φ) := by
    intro U hU
    have hU' := hW.isOpenMap_subtype_val U hU
    apply isOpen_iff_mem_nhds.2
    rintro _ ⟨p, hp, rfl⟩
    change W.domRestrict Φ '' U ∈ 𝓝 (Φ p)
    rw [← hLocal.map_nhds_eq (hWD p.property)]
    have hImg : Φ '' (Subtype.val '' U) ∈ map Φ (𝓝 (p : X)) :=
      image_mem_map (hU'.mem_nhds ⟨p, hp, rfl⟩)
    change (fun x : W => Φ x) '' U ∈ map Φ (𝓝 (p : X))
    simpa only [Set.image_image] using hImg
  let pe := BijOn.toPartialEquiv Φ W (Φ '' W)
    ⟨mapsTo_image _ _, hInj.mono hWD, surjOn_image _ _⟩
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    (hLocal.continuousOn.mono hWD) hOpen hW
  exact ⟨e, rfl, image_subset_iff.mpr (fun _ hp => hMaps (hWD hp)),
    (fun p hp => hEval p (hWD hp)), hAgree⟩

end OpenGlue

variable {n : ℕ} [NeZero n] {M₁ M₂ F : Type*}
  [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n

/-- Agreement near each point with a smooth local isometry gives a
smooth local isometry, including smoothness of the inverse. -/
theorem isLocalMetricIsometry_of_local_agreement
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂} (e : OpenPartialHomeomorph M₂ M₁)
    (hCover : ∀ p ∈ e.source, ∃ f : OpenPartialHomeomorph M₂ M₁,
      p ∈ f.source ∧ IsLocalMetricIsometry g₁ g₂ f ∧ (e : M₂ → M₁) =ᶠ[𝓝 p] f) :
    IsLocalMetricIsometry g₁ g₂ e := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨f, hpf, hf, hEq⟩ := hCover p hp
    exact ((hf.smooth.contMDiffAt (f.open_source.mem_nhds hpf)).congr_of_eventuallyEq hEq).contMDiffWithinAt
  · intro q hq
    let p := e.symm q
    have hp := e.map_target hq
    obtain ⟨f, hpf, hf, hEq⟩ := hCover p hp
    obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
      (inter_mem (inter_mem (e.open_source.mem_nhds hp) (f.open_source.mem_nhds hpf)) hEq)
    have hVe : V ⊆ e.source := fun _ hx => (hVsub hx).1.1
    have hVf : V ⊆ f.source := fun _ hx => (hVsub hx).1.2
    have hqImg : q ∈ e '' V := ⟨p, hpV, e.right_inv hq⟩
    have hEqInv : (e.symm : M₁ → M₂) =ᶠ[𝓝 q] f.symm := by
      filter_upwards [(e.isOpen_image_of_subset_source hV hVe).mem_nhds hqImg] with y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [e.left_inv (hVe hx), (show e x = f x from (hVsub hx).2), f.left_inv (hVf hx)]
    have hqf : q ∈ f.target := by
      have hqp := f.map_source hpf
      have hpfq : f p = q := hEq.eq_of_nhds.symm.trans (e.right_inv hq)
      rwa [hpfq] at hqp
    exact ((hf.smooth_inverse.contMDiffAt (f.open_target.mem_nhds hqf)).congr_of_eventuallyEq
      hEqInv).contMDiffWithinAt
  · intro p hp v w
    obtain ⟨f, hpf, hf, hEq⟩ := hCover p hp
    let D := mfderiv J J f p
    have hD (t : CalderonN.X n) : (mfderiv J J e p t : CalderonN.X n) = D t :=
      congrArg (fun L : CalderonN.X n →L[ℝ] CalderonN.X n => L t) hEq.mfderiv_eq
    calc
      _ = g₁.inner (f p) (D v) (D w) := hf.metric_eq p hpf v w
      _ = g₁.inner (e p) (D v) (D w) :=
        congrArg (fun y : M₁ => g₁.inner y (D v) (D w)) hEq.eq_of_nhds.symm
      _ = _ := congrArg₂ (fun a b : CalderonN.X n => g₁.inner (e p) a b) (hD v).symm (hD w).symm

/-- The component of the matching domain containing the seed carries a
single smooth local isometry respecting every evaluation. -/
theorem exists_seedComponent_isometry [LocallyConnectedSpace M₂]
    (I₂ : SourceEvaluations M₂ F) (I₁ : SourceEvaluations M₁ F)
    (g₁ : SmoothMetric n M₁) (g₂ : SmoothMetric n M₂)
    (Seed : EvaluationMatch I₂ I₁ (IsLocalMetricIsometry g₁ g₂))
    (s : M₂) :
    let D := matchingDomain I₂ I₁ (IsLocalMetricIsometry g₁ g₂)
    let W := connectedComponentIn D s
    ∃ e : OpenPartialHomeomorph M₂ M₁, e.source = W ∧
      e.target ⊆ I₁.interior ∧ IsLocalMetricIsometry g₁ g₂ e ∧
      (∀ p ∈ W, I₂.value p = I₁.value (e p)) ∧
      ∀ E : EvaluationMatch I₂ I₁ (IsLocalMetricIsometry g₁ g₂), EqOn e E.chart E.chart.source := by
  let D := matchingDomain I₂ I₁ (IsLocalMetricIsometry g₁ g₂)
  let W := connectedComponentIn D s
  have hW : IsOpen W := (matchingDomain_isOpen I₂ I₁ (IsLocalMetricIsometry g₁ g₂)).connectedComponentIn
  have hWD : W ⊆ D := connectedComponentIn_subset D s
  let _ : Nonempty M₂ := ⟨s⟩
  obtain ⟨e, hsource, htarget, hEval, hAgree⟩ :=
    exists_evaluationMatch_on_open_subset I₂ I₁ (IsLocalMetricIsometry g₁ g₂)
      (Seed.chart s) hW hWD
  refine ⟨e, hsource, htarget, isLocalMetricIsometry_of_local_agreement e ?_, hEval, hAgree⟩
  intro p hp
  obtain ⟨E, hpE⟩ := mem_matchingDomain.mp (hWD (hsource ▸ hp))
  exact ⟨E.chart, hpE, E.property, Filter.mem_of_superset (E.chart.open_source.mem_nhds hpE)
    (fun _ hx => hAgree E hx)⟩

end CalderonPatch
