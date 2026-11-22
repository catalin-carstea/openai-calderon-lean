module

public import Proof.Manuscript.Lemma21

public section

open MeasureTheory Set
open scoped ContDiff Manifold
open CalderonN (I chartDerivativeWord)
open CalderonPatch

namespace CalderonPaper

theorem boundaryMixedJetAtMeasuredPoint {m : ℕ} (hn : 3 ≤ m + 1) {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (d₁ d₂ : DirichletData m M)
    {Γ : Set ((𝓡∂ (m+1)).boundary M)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    (hEnergy : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    (p : (𝓡∂ (m+1)).boundary M) (hp : p ∈ Γ)
    (B : PairedNativeBoundaryBox d₁.metric d₂.metric Γ p)
    (k : Fin m) (i j : I (m+1)) :
    chartDerivativeWord [Fin.succAbove 0 k, 0] (fun z => B.first.field z i j)
        (normalFacePoint (normalTangentialCoordinates (B.second.coord p))) =
      chartDerivativeWord [Fin.succAbove 0 k, 0] (fun z => B.second.field z i j)
        (normalFacePoint (normalTangentialCoordinates (B.second.coord p))) :=
  lemma21 hn d₁ d₂ hΓ hΓne hEnergy p hp B [Fin.succAbove 0 k, 0] i j B.center_box

end CalderonPaper
