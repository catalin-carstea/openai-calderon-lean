module

public import Proof.CalderonPatch.CompletedMetric
public import Proof.CalderonPatch.InteriorCompletion

@[expose] public section

noncomputable section
open Filter Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [CompactSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [CompactSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- The normal-flow representation near one boundary point.
\`level\` moves points to a fixed positive interior level and \`flow\`
reconstructs the point with the prescribed height on the other side. -/
structure NormalFlowRepresentation (f : M₂ → M₁) (p : M₂) where
  domain : Set M₂
  open_domain : IsOpen domain
  center : p ∈ domain
  level : M₂ → M₂
  height : M₂ → ℝ
  flow : M₁ × ℝ → M₁
  flow_domain : Set (M₁ × ℝ)
  smooth_level : ContMDiffOn J J ∞ level domain
  smooth_height : ContMDiffOn J R ∞ height domain
  smooth_flow : ContMDiffOn (ModelWithCorners.prod J R) J ∞ flow flow_domain
  level_interior : MapsTo level domain ((𝓡∂ n).interior M₂)
  flow_defined : MapsTo (fun x => (f (level x), height x)) domain flow_domain
  agreement : ∀ x ∈ domain ∩ (𝓡∂ n).interior M₂, flow (f (level x), height x) = f x

/-- The continuous extension is smooth wherever normal coordinates
express it by the interior level map and smooth normal flow. -/
theorem contMDiff_of_normalFlowRepresentation (f : M₂ → M₁) (hf : Continuous f)
    (hi : ContMDiffOn J J ∞ f ((𝓡∂ n).interior M₂))
    (hFlow : ∀ p ∈ (𝓡∂ n).boundary M₂, Nonempty (NormalFlowRepresentation (n := n) f p)) :
    ContMDiff J J ∞ f := by
  intro p
  by_cases hp : p ∈ (𝓡∂ n).interior M₂
  · exact hi.contMDiffAt (((𝓡∂ n).isOpen_interior (n := ∞) (by simp)).mem_nhds hp)
  · have hpB : p ∈ (𝓡∂ n).boundary M₂ := by
      rw [← (𝓡∂ n).compl_interior]
      exact hp
    obtain ⟨C⟩ := hFlow p hpB
    let g : M₂ → M₁ := fun x => C.flow (f (C.level x), C.height x)
    have hg : ContMDiffOn J J ∞ g C.domain :=
      C.smooth_flow.comp ((hi.comp C.smooth_level C.level_interior).prodMk C.smooth_height) C.flow_defined
    let V := C.domain ∩ (𝓡∂ n).interior M₂
    have hNear : EqOn g f C.domain := by
      intro x hx
      have hcl : x ∈ closure V := by
        rw [mem_closure_iff_frequently]
        have hI := mem_closure_iff_frequently.mp (dense_manifoldInterior (n := n) (M := M₂) x)
        exact (hI.and_eventually (C.open_domain.mem_nhds hx)).mono (fun _ h => ⟨h.2, h.1⟩)
      let _ : NeBot (𝓝[V] x) := mem_closure_iff_nhdsWithin_neBot.mp hcl
      have hgt : Tendsto g (𝓝[V] x) (𝓝 (g x)) :=
        ((hg.continuousOn.continuousAt (C.open_domain.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds)
      have hft : Tendsto f (𝓝[V] x) (𝓝 (f x)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact tendsto_nhds_unique_of_eventuallyEq hgt hft
        (Filter.mem_of_superset self_mem_nhdsWithin (fun _ hy => C.agreement _ hy))
    have hEq : f =ᶠ[𝓝 p] g :=
      Filter.mem_of_superset (C.open_domain.mem_nhds C.center) (fun _ hx => (hNear hx).symm)
    exact (hg.contMDiffAt (C.open_domain.mem_nhds C.center)).congr_of_eventuallyEq hEq

/-- The homeomorphic completion is a smooth metric isometry when the
normal-flow representations are available on both boundary collars. -/
theorem smoothCompletion_of_normalFlowRepresentations
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    {e : OpenPartialHomeomorph M₂ M₁} (he : IsLocalMetricIsometry g₁ g₂ e)
    (hs : e.source = (𝓡∂ n).interior M₂) (ht : e.target = (𝓡∂ n).interior M₁)
    (hFlow : ∀ f : M₂ ≃ₜ M₁, EqOn f e e.source → EqOn f.symm e.symm e.target →
      (∀ p ∈ (𝓡∂ n).boundary M₂, Nonempty (NormalFlowRepresentation (n := n) f p)) ∧
      (∀ q ∈ (𝓡∂ n).boundary M₁, Nonempty (NormalFlowRepresentation (n := n) f.symm q))) :
    ∃ f : M₂ ≃ₘ⟮J, J⟯ M₁, EqOn f e e.source ∧
      ∀ p (v w : TangentSpace J p), g₂.inner p v w =
        g₁.inner (f p) (mfderiv J J f p v) (mfderiv J J f p w) := by
  obtain ⟨f, hf, hfs⟩ := interiorIsometry_extends_homeomorph he hs ht
  obtain ⟨h₂, h₁⟩ := hFlow f hf hfs
  have hF := contMDiff_of_normalFlowRepresentation f f.continuous
    (hs ▸ he.smooth.congr hf) h₂
  have hFi := contMDiff_of_normalFlowRepresentation f.symm f.symm.continuous
    (ht ▸ he.smooth_inverse.congr hfs) h₁
  let Φ : M₂ ≃ₘ⟮J, J⟯ M₁ :=
    { f.toEquiv with contMDiff_toFun := hF, contMDiff_invFun := hFi }
  exact ⟨Φ, hf, pullbackMetric_of_interior_agreement he hs hF hf⟩

end CalderonPatch
