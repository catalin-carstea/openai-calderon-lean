module

public import Proof.CalderonPatch.MeasuredBoundaryJets
public import Proof.CalderonPatch.PairedNativeBoundaryBox

public section

open MeasureTheory Set
open scoped ContDiff Manifold
open CalderonN (I chartDerivativeWord)
open CalderonPatch

namespace CalderonPaper

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
        (tangentialBox B.boxLower B.boxUpper) := sorry

end CalderonPaper
