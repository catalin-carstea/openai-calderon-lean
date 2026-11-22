module

public import Proof.CalderonPatch.GreenOffPole
public import Proof.CalderonPatch.IsometricCharts
public import Proof.CalderonPatch.ManifoldContinuation
public import Proof.CalderonPatch.PuncturedInterior

import Proof.CalderonN.GreenWeak

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (X IsDirichletGreenKernel Harmonic laplace_congrOn)

variable {n : ℕ} [NeZero n] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [T2Space M₁] [MeasurableSpace M₁] [BorelSpace M₁]
  [ChartedSpace (EuclideanHalfSpace n) M₁] [IsManifold (𝓡∂ n) ∞ M₁]
  [TopologicalSpace M₂] [T2Space M₂] [MeasurableSpace M₂] [BorelSpace M₂]
  [ChartedSpace (EuclideanHalfSpace n) M₂] [IsManifold (𝓡∂ n) ∞ M₂]

local notation "J" => 𝓡∂ n

/-- Agreement of the actual Dirichlet kernels against cap sources extends
from the seed region to every matched off-diagonal pair. For a fixed
pole both sections satisfy the same harmonic equation on the connected
punctured matching domain. -/
theorem green_eqOn_matchedDomain (hn : 2 ≤ n)
    {g₁ : SmoothMetric n M₁} {g₂ : SmoothMetric n M₂}
    (Φ : OpenPartialHomeomorph M₂ M₁) (hΦ : IsLocalMetricIsometry g₁ g₂ Φ)
    (hI₂ : Φ.source ⊆ (𝓡∂ n).interior M₂) (hI₁ : Φ.target ⊆ (𝓡∂ n).interior M₁)
    (hW : IsConnected Φ.source)
    {μ₁ : Measure M₁} {μ₂ : Measure M₂} (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    {G₁ : M₁ × M₁ → ℝ} {G₂ : M₂ × M₂ → ℝ}
    (hG₁ : IsDirichletGreenKernel J μ₁ (nativeLaplace g₁) G₁)
    (hG₂ : IsDirichletGreenKernel J μ₂ (nativeLaplace g₂) G₂)
    {V : Set M₂} (hV : IsOpen V) (hVc : IsConnected V) (hVW : V ⊆ Φ.source)
    (hSeed : ∀ q ∈ Φ.source, ∀ x ∈ V, x ≠ q → G₁ (Φ x, Φ q) = G₂ (x, q)) :
    ∀ q ∈ Φ.source, ∀ x ∈ Φ.source, x ≠ q → G₁ (Φ x, Φ q) = G₂ (x, q) := by
  intro q hq
  let W := Φ.source
  let U : Set M₂ := W \ {q}
  let A : Set M₂ := V \ {q}
  let u : M₂ → ℝ := fun x => G₁ (Φ x, Φ q)
  let v : M₂ → ℝ := fun x => G₂ (x, q)
  have hU : IsOpen U := Φ.open_source.sdiff isClosed_singleton
  have hUC : IsConnected U :=
    isConnected_interior_sdiff_finite hn Φ.open_source hW hI₂ (finite_singleton q)
  have hA : IsOpen A := hV.sdiff isClosed_singleton
  have hAC : IsConnected A :=
    isConnected_interior_sdiff_finite hn hV hVc (hVW.trans hI₂) (finite_singleton q)
  have hAsub : A ⊆ U := fun _ hx => ⟨hVW hx.1, hx.2⟩
  have hSeedEq : EqOn u v A :=
    fun _ hx => hSeed q hq _ hx.1 (fun he => hx.2 (mem_singleton_iff.mpr he))
  have hEq : EqOn u v U := by
    apply eqOn_of_locally_harmonic (n := n) hU hUC hA hAC.1 hAsub hSeedEq
    intro p hp
    obtain ⟨b, hpb, hbU, hbI, hb, hbs⟩ := exists_interiorChart p (hI₂ hp.1) hU hp
    have hbW : b.source ⊆ W := hbU.trans sdiff_subset
    obtain ⟨a, hT, hS, hInv, ha, has, hmetric⟩ := exists_transported_chart hΦ b hbW hb hbs
    have haI : a.source ⊆ (𝓡∂ n).interior M₁ := by
      rw [hS]
      rintro _ ⟨x, hx, rfl⟩
      exact hI₁ (Φ.map_source (hbW hx))
    have hqa : Φ q ∉ a.source := by
      rw [hS]
      rintro ⟨x, hx, hEq⟩
      exact (hbU hx).2 (mem_singleton_iff.mpr (Φ.injOn (hbW hx) hq hEq))
    have hqb : q ∉ b.source := fun h => (hbU h).2 (mem_singleton q)
    let C₁ := nativeInteriorMetricChart g₁ μ₁ hμ₁ a haI ha has
    let C₂ := nativeInteriorMetricChart g₂ μ₂ hμ₂ b hbI hb hbs
    have h₁ : Harmonic a.target (coordinateMetric g₁ a) (fun x => G₁ (a.symm x, Φ q)) :=
      harmonic_greenSection_off_pole C₁ (fun f _ => tsupport_nativeLaplace_subset g₁ f) hG₁
        (hI₁ (Φ.map_source hq)) hqa
    have h₂ : Harmonic b.target (coordinateMetric g₂ b) (v ∘ b.symm) :=
      harmonic_greenSection_off_pole C₂ (fun f _ => tsupport_nativeLaplace_subset g₂ f) hG₂ (hI₂ hq) hqb
    have h₁' : Harmonic b.target (coordinateMetric g₁ a) (u ∘ b.symm) := by
      rw [hT, hInv] at h₁
      exact h₁
    refine ⟨b, hpb, hbU, coordinateMetric g₂ b, C₂.smooth_metric, ⟨h₁'.1, ?_⟩, h₂⟩
    intro x hx
    exact (laplace_congrOn b.open_target hmetric (fun _ _ => rfl) hx).symm.trans (h₁'.2 x hx)
  exact fun x hx hne => hEq ⟨hx, fun he => hne (mem_singleton_iff.mp he)⟩

end CalderonPatch
