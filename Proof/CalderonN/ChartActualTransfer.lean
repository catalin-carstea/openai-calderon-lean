module

public import Proof.CalderonN.ChartTransferAssembly
public import Proof.CalderonN.GlobalChartReduction

import Proof.CalderonN.ConformalGreenDensityEstimate
import Proof.CalderonN.ConformalGreenDensityJets
import Proof.CalderonN.ConformalActualGreenTransfer
import Proof.CalderonN.ChartNormalization
import Proof.CalderonN.ShrinkingRadiusParameter
import Mathlib.Tactic

public section

noncomputable section
open Filter Metric Set
open scoped Topology ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- The scaled data on the actual continued kernel supply the transfer density
and its uniform cutoff estimate on the same sphere family. -/
theorem uniformTransferFromScaledData_actual (hn : 3 ≤ dim) : UniformTransferFromScaledData normal := by
  intro U W Z hU hside q₁ q₂ hq₁ hq₂ _ _ hcoord₁ hcoord₂ G₁ G₂ hG₁ _ _ _
    m v₁ v₂ hv₁ hv₂ hpair E hE p hp ρ R ε tb K c₀ floor hρ hR hε _ hK _ _ hCZ _ hN hRZ
    k M Cj hSetup hData
  let Y := interior (coordinateCylinder normal)
  have hY' : Y ⊆ interior Z := interior_subset.trans hCZ
  have hNormalZ (lam : ℝ) (hlam : lam ∈ Icc (-1 : ℝ) 1) :=
    (hN lam hlam).mono_centers (interior_subset : interior Z ⊆ Z)
  have hRadius (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (y : X dim) (hy : y ∈ Y) :
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2 :=
    hRZ δ hδ y (interior_subset (hY' hy))
  have hJets := uniformCylinderGreenDensityJets_of_scaledData hq₁ hq₂ hE hCZ
    (show 1 ≤ p by omega) hρ hR hε.le hNormalZ hRadius hData
  have hBound := uniformActualCylinderGreenTraceBound_of_densityJets hq₁ hq₂ hE
    isOpen_interior hCZ (show 1 ≤ p by omega) hρ hR hε.le hNormalZ hRadius hJets
  have hR' (δ : ℝ) (hδ : δ ∈ Ioc (0 : ℝ) 1) (y : X dim) (hy : y ∈ Y) :
      0 < shrinkingRadius R p (conformalDepth normal 4) δ y ∧
      shrinkingRadius R p (conformalDepth normal 4) δ y < ρ :=
    ⟨shrinkingRadius_pos hR hδ.1 p _ y, (hRadius δ hδ y hy).trans_lt (half_lt_self hρ)⟩
  have hFlux := conformalCylinderGreenFluxDensity_of_actualTraceBound hq₁ hq₂ hE
    (fun lam hlam => (hNormalZ lam hlam).mono_centers hY') hR' hBound
  exact conformalCylinderTransfer_of_uniformGreenFluxDensity hn hU hside hY'
    hq₁ hq₂ hcoord₁ hcoord₂ hG₁ hv₁ hv₂ hpair hE hρ hK hSetup hFlux

/-- The normalized chart conclusion uses Proposition 5.3 at the same dimension. -/
theorem normalizedLocalMetricExtension_of_coercivity (hn : 3 ≤ dim)
    (hCoercivity : Coercivity dim) : NormalizedLocalMetricExtension normal :=
  normalizedLocalMetricExtension_of_global
    (globalNormalizedLocalMetricExtension_of_scaled_transfer hn hCoercivity
      (uniformTransferFromScaledData_actual (normal := normal) hn))

end CalderonN
