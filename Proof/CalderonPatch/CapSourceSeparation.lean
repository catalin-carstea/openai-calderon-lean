module

public import Proof.CalderonPatch.CapGreenAgreement
public import Proof.CalderonPatch.InteriorTests
public import Proof.CalderonPatch.EvaluationFrontier

import Proof.CalderonN.GreenRestriction

@[expose] public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch

open CalderonN (X Harmonic InteriorMetricChart IsDirichletGreenKernel)

variable {n : ℕ} [NeZero n] {M F : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

/-- The representation of the common smooth cap sources on one side of
the extension. The source label in the evaluation is that of the test
in the displayed Green pairing. -/
structure CapSourceRepresentation (E : M → F → ℝ) (G : M × M → ℝ) where
  chart : OpenPartialHomeomorph M (X n)
  domain : Set (X n)
  open_domain : IsOpen domain
  connected_domain : IsConnected domain
  domain_subset : domain ⊆ chart.target
  interior : MapsTo chart.symm domain ((𝓡∂ n).interior M)
  density : X n → ℝ
  density_continuous : ContinuousOn density domain
  density_positive : ∀ x ∈ domain, 0 < density x
  representation : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ domain →
    ∃ s : F, ∀ p ∈ (𝓡∂ n).interior M,
      E p s = ∫ x in domain, φ x * G (chart.symm x, p) * density x

/-- Equality of cap test pairings determines smooth harmonic functions
on the interior with any finite set of poles removed. -/
theorem eqOn_puncturedInterior_of_cap_tests (hn : 2 ≤ n) [ConnectedSpace M]
    (g : SmoothMetric n M) (μ : Measure M) (hμ : IsMetricVolume g μ)
    {E : M → F → ℝ} {G : M × M → ℝ} (C : CapSourceRepresentation (n := n) E G)
    {K : Set M} (hK : K.Finite) {u v : M → ℝ}
    (hu : ContinuousOn u ((𝓡∂ n).interior M \ K)) (hv : ContinuousOn v ((𝓡∂ n).interior M \ K))
    (hTest : ∀ φ : X n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ (C.domain ∩ C.chart.symm ⁻¹' Kᶜ) →
      (∫ x in C.domain, φ x * u (C.chart.symm x) * C.density x) =
        ∫ x in C.domain, φ x * v (C.chart.symm x) * C.density x)
    (hH : ∀ A : InteriorMetricChart J μ (nativeLaplace g),
      A.chart.source ⊆ (𝓡∂ n).interior M \ K →
      Harmonic A.chart.target A.metric (u ∘ A.chart.symm) ∧
        Harmonic A.chart.target A.metric (v ∘ A.chart.symm)) :
    EqOn u v ((𝓡∂ n).interior M \ K) := by
  let V := C.domain ∩ C.chart.symm ⁻¹' Kᶜ
  let T := C.chart.symm '' C.domain
  let A := C.chart.symm '' V
  let U := (𝓡∂ n).interior M \ K
  have hV : IsOpen V :=
    (C.chart.continuousOn_symm.mono C.domain_subset).isOpen_inter_preimage
      C.open_domain hK.isClosed.isOpen_compl
  have hVs : V ⊆ C.domain := inter_subset_left
  have hT : IsOpen T := C.chart.isOpen_image_symm_of_subset_target C.open_domain C.domain_subset
  have hTc : IsConnected T :=
    C.connected_domain.image C.chart.symm (C.chart.continuousOn_symm.mono C.domain_subset)
  have hTI : T ⊆ (𝓡∂ n).interior M := image_subset_iff.mpr C.interior
  have hA : IsOpen A := C.chart.isOpen_image_symm_of_subset_target hV (hVs.trans C.domain_subset)
  have hAid : A = T \ K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨mem_image_of_mem _ hz.1, hz.2⟩
    · rintro ⟨⟨z, hz, rfl⟩, h⟩
      exact ⟨z, ⟨hz, h⟩, rfl⟩
  have hAc : IsConnected A :=
    hAid.symm ▸ isConnected_interior_sdiff_finite hn hT hTc hTI hK
  have hAeq : EqOn u v A := by
    have hmap : MapsTo C.chart.symm V U := fun _ hz => ⟨C.interior hz.1, hz.2⟩
    have hcts := C.chart.continuousOn_symm.mono (hVs.trans C.domain_subset)
    have h := eqOn_of_weighted_test_pairings hV hVs (C.density_continuous.mono hVs)
      (fun x hx => C.density_positive x hx.1) (hu.comp hcts hmap) (hv.comp hcts hmap) hTest
    rintro _ ⟨z, hz, rfl⟩
    exact h hz
  have hI := (𝓡∂ n).isOpen_interior (M := M) (n := ∞) (by simp)
  have hU : IsOpen U := hI.sdiff hK.isClosed
  have hUc : IsConnected U :=
    isConnected_interior_sdiff_finite hn hI isConnected_manifoldInterior Subset.rfl hK
  apply eqOn_of_locally_harmonic (n := n) hU hUc hA hAc.1
    (hAid.symm ▸ (show T \ K ⊆ U from fun _ hx => ⟨hTI hx.1, hx.2⟩)) hAeq
  intro p hp
  obtain ⟨e, hpe, heU, heI, he, hei⟩ := exists_interiorChart p hp.1 hU hp
  let D := nativeInteriorMetricChart g μ hμ e heI he hei
  exact ⟨e, hpe, heU, D.metric, D.smooth_metric, hH D heU⟩

omit [T2Space M] [BorelSpace M] in
private theorem integral_kernelPair_eq_of_eqOn {g : SmoothMetric n M} {μ : Measure M}
    {K : Set M} (hK : μ K = 0) {u v : M → ℝ}
    (hEq : EqOn u v ((𝓡∂ n).interior M \ K)) {φ : M → ℝ}
    (hφ : tsupport φ ⊆ (𝓡∂ n).interior M) :
    (∫ x, u x * (-nativeLaplace g φ x) ∂μ) = ∫ x, v x * (-nativeLaplace g φ x) ∂μ := by
  have hAE : ∀ᵐ x ∂μ, x ∉ K := ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hK)
  apply integral_congr_ae
  filter_upwards [hAE] with x hx
  by_cases hi : x ∈ (𝓡∂ n).interior M
  · rw [hEq ⟨hi, hx⟩]
  · have hzero : nativeLaplace g φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hi (hφ (tsupport_nativeLaplace_subset g φ h)))
    simp [hzero]

/-- A normalized Green inverse and continuation forbid the zero
evaluation at an interior point. -/
theorem capEvaluation_ne_zero (hn : 2 ≤ n) [ConnectedSpace M]
    {g : SmoothMetric n M} {μ : Measure M} (hμ : IsMetricVolume g μ)
    {E : M → F → ℝ} {G : M × M → ℝ} (C : CapSourceRepresentation (n := n) E G)
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    {p : M} (hp : p ∈ (𝓡∂ n).interior M) : E p ≠ 0 := by
  intro hZero
  have hEq : EqOn (fun x => G (x, p)) 0 ((𝓡∂ n).interior M \ {p}) := by
    apply eqOn_puncturedInterior_of_cap_tests hn g μ hμ C (finite_singleton p)
      ((hG.continuous_off_pole p hp).mono (sdiff_subset_compl _ _)) continuousOn_const
    · intro φ hφ hc hs
      obtain ⟨a, ha⟩ := C.representation φ hφ hc (hs.trans inter_subset_left)
      have h : E p a = 0 := congrFun hZero a
      refine (ha p hp).symm.trans ?_
      change E p a = ∫ x in C.domain, φ x * (0 : ℝ) * C.density x
      simp [h]
    · intro A hA
      refine ⟨harmonic_greenSection_off_pole A (fun u _ => tsupport_nativeLaplace_subset g u) hG
        hp (fun h => (hA h).2 (mem_singleton p)), ?_⟩
      refine ⟨contDiffOn_const, ?_⟩
      intro x _
      have hc (i : CalderonN.I n) : CalderonN.coordDeriv i (0 : X n → ℝ) = 0 := by
        funext y
        simp [CalderonN.coordDeriv, Pi.zero_def]
      change CalderonN.laplace A.metric 0 x = 0
      simp [CalderonN.laplace, hc]
  obtain ⟨φ, hφ, hc, hs, hφp⟩ :=
    exists_compactly_supported_interior_test hp isOpen_univ (mem_univ p)
  have hWeak := (hG.weak_inverse p hp φ hφ hc (hs.trans inter_subset_right)).2
  have hNull := metricVolume_singleton_interior g μ hμ hp
  have hIntegral := integral_kernelPair_eq_of_eqOn (g := g) hNull hEq (hs.trans inter_subset_right)
  rw [hWeak, hφp] at hIntegral
  change (1 : ℝ) = ∫ x, (0 : ℝ) * (-nativeLaplace g φ x) ∂μ at hIntegral
  simp at hIntegral

/-- Distinct interior poles have distinct evaluations on the common
source family, by the weak inverse law tested away from one pole. -/
theorem capEvaluation_injOn (hn : 2 ≤ n) [ConnectedSpace M]
    {g : SmoothMetric n M} {μ : Measure M} (hμ : IsMetricVolume g μ)
    {E : M → F → ℝ} {G : M × M → ℝ} (C : CapSourceRepresentation (n := n) E G)
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G) :
    InjOn E ((𝓡∂ n).interior M) := by
  intro p hp q hq hE
  by_contra hne
  let K : Set M := {p, q}
  have hK : K.Finite := (finite_singleton q).insert p
  have hpK : p ∈ K := by simp [K]
  have hqK : q ∈ K := by simp [K]
  have hEq : EqOn (fun x => G (x, p)) (fun x => G (x, q)) ((𝓡∂ n).interior M \ K) := by
    apply eqOn_puncturedInterior_of_cap_tests hn g μ hμ C hK
      ((hG.continuous_off_pole p hp).mono (fun _ hx h => hx.2 ((mem_singleton_iff.mp h).symm ▸ hpK)))
      ((hG.continuous_off_pole q hq).mono (fun _ hx h => hx.2 ((mem_singleton_iff.mp h).symm ▸ hqK)))
    · intro φ hφ hc hs
      obtain ⟨a, ha⟩ := C.representation φ hφ hc (hs.trans inter_subset_left)
      exact (ha p hp).symm.trans ((congrFun hE a).trans (ha q hq))
    · intro A hA
      exact ⟨harmonic_greenSection_off_pole A (fun u _ => tsupport_nativeLaplace_subset g u) hG
        hp (fun h => (hA h).2 hpK),
        harmonic_greenSection_off_pole A (fun u _ => tsupport_nativeLaplace_subset g u) hG
        hq (fun h => (hA h).2 hqK)⟩
  have hpU : p ∈ ({q} : Set M)ᶜ := fun h => hne (mem_singleton_iff.mp h)
  obtain ⟨φ, hφ, hc, hs, hφp⟩ :=
    exists_compactly_supported_interior_test hp isClosed_singleton.isOpen_compl hpU
  have hφq : φ q = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (hs h).1 (mem_singleton q))
  have hWeak₁ := (hG.weak_inverse p hp φ hφ hc (hs.trans inter_subset_right)).2
  have hWeak₂ := (hG.weak_inverse q hq φ hφ hc (hs.trans inter_subset_right)).2
  have hNull : μ K = 0 := measure_union_null (metricVolume_singleton_interior g μ hμ hp)
    (metricVolume_singleton_interior g μ hμ hq)
  have hIntegral := integral_kernelPair_eq_of_eqOn (g := g) hNull hEq (hs.trans inter_subset_right)
  rw [hWeak₁, hWeak₂, hφp, hφq] at hIntegral
  exact one_ne_zero hIntegral

/-- The Green representations produce the evaluation data used in the
matching relation once the actual solutions are continuous and vanish
on the extended boundary. -/
def sourceEvaluations_of_capSolutions (hn : 2 ≤ n) [ConnectedSpace M]
    {g : SmoothMetric n M} {μ : Measure M} (hμ : IsMetricVolume g μ)
    {E : M → F → ℝ} {G : M × M → ℝ} (C : CapSourceRepresentation (n := n) E G)
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hE : Continuous E) (hBoundary : EqOn E 0 ((𝓡∂ n).boundary M)) : SourceEvaluations M F where
  interior := (𝓡∂ n).interior M
  value := E
  continuous := hE
  interior_ne_zero _ hp := capEvaluation_ne_zero hn hμ C hG hp
  zero_outside_interior _ hp := by
    apply hBoundary
    rw [← (𝓡∂ n).compl_interior]
    exact hp
  separates := capEvaluation_injOn hn hμ C hG

end CalderonPatch
