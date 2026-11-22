module

public import Proof.CalderonN.ConformalActualGreenTransfer
public import Proof.CalderonN.ConformalScaledGreenDataJets

import Proof.CalderonN.ConformalGreenDensityEstimate
import Proof.CalderonN.ConformalGreenDensityJets
import Mathlib.Tactic.NormNum

public section

open CalderonN Metric Set
open scoped ContDiff

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Realize the continued Green datum on the fixed cylinder as a uniform
conormal density with the actual moving-trace residual. -/
theorem uniformConformalCylinderGreenFlux {normal : I dim}
    {W Z : Set (X dim)} {g₁ g₂ : MetricField dim} (hg₁ : SmoothMetric univ g₁)
    (hg₂ : SmoothMetric univ g₂) {G₁ G₂ : X dim × X dim → ℝ}
    {E : ℝ → X dim × X dim → X dim}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {p : ℕ} (hp : 1 ≤ p) {ρ R ε tb : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hCZ : coordinateCylinder normal ⊆ interior Z)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Z (ball (0 : X dim) 3)
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Z,
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ / 2)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W (interior Z) G₁ G₂ E
      p ρ R ε tb (2 * dim + 8)) :
    UniformCylinderGreenFluxDensity normal g₁ g₂ W (interior Z) G₁ G₂ E p ρ R ε tb := by
  let Y := interior (coordinateCylinder normal)
  have hYZ : Y ⊆ interior Z := interior_subset.trans hCZ
  have hNormalZ (lam : ℝ) (hlam : lam ∈ Icc (-1 : ℝ) 1) :=
    (hNormal lam hlam).mono_centers (interior_subset : interior Z ⊆ Z)
  have hRadiusY (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (y : X dim) (hy : y ∈ Y) :=
    hRadius δ hδ y (interior_subset (hYZ hy))
  have hJets := uniformCylinderGreenDensityJets_of_scaledData hg₁ hg₂ hE hCZ
    hp hρ hR hε hNormalZ hRadiusY hData
  have hResidual := uniformActualCylinderGreenTraceBound_of_densityJets hg₁ hg₂ hE
    isOpen_interior hCZ hp hρ hR hε hNormalZ hRadiusY hJets
  have hRadiusPositive (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (y : X dim) (hy : y ∈ Y) :
      0 < shrinkingRadius R p (conformalDepth normal 4) δ y ∧
        shrinkingRadius R p (conformalDepth normal 4) δ y < ρ :=
    ⟨shrinkingRadius_pos hR hδ.1 p _ y, (hRadiusY δ hδ y hy).trans_lt (half_lt_self hρ)⟩
  exact conformalCylinderGreenFluxDensity_of_actualTraceBound hg₁ hg₂ hE
    (fun lam hlam => (hNormalZ lam hlam).mono_centers hYZ) hRadiusPositive hResidual

end CalderonPaper
