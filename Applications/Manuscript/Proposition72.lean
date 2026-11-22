module

public import Proof.Manuscript.Proposition72

public section

open Set
open scoped ContDiff Manifold
open CalderonPatch

namespace CalderonPaper

/-- The completion maps the original copies onto one another pointwise
at every original point of the measured boundary. -/
theorem completedIsometryAtMeasuredPoint {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    {d₁ d₂ : DirichletData m M}
    {Γ : Set ((𝓡∂ (m+1)).boundary M)} (hΓ : IsOpen Γ)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (C : MeasuredCommonCap d₁ d₂ Γ)
    (e : OpenPartialHomeomorph M M)
    (hSource : e.source = (𝓡∂ (m+1)).interior M)
    (hTarget : e.target = (𝓡∂ (m+1)).interior M)
    (hIsometry : IsLocalMetricIsometry C.firstMetric C.secondMetric e)
    (hCap : EqOn e C.capMap C.capMap.source) :
    ∃ Φ : M ≃ₘ⟮𝓡∂ (m+1), 𝓡∂ (m+1)⟯ M,
      EqOn Φ e e.source ∧ ∀ p ∈ Γ, Φ (C.secondCopy.embed p) = C.firstCopy.embed p := by
  obtain ⟨Φ, hExtend, _, Ψ, hCopy, _, hFix⟩ :=
    proposition72 hn hΓ hEnergy C e hSource hTarget hIsometry hCap
  refine ⟨Φ, hExtend, ?_⟩
  intro p hp
  have h := congrFun hCopy (p : M)
  change C.firstCopy.embed (Ψ p) = Φ (C.secondCopy.embed p) at h
  rw [hFix p hp] at h
  exact h.symm

end CalderonPaper
