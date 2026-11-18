import Proof.EffectiveFirstAdjointFiveHalfBudgetContinuous
import Proof.EffectiveFirstAdjointFiveHalfMeasurability
import Proof.CompactSupportedMeasurableMajorant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection_memLp
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) (p : ℝ≥0∞) :
    MemLp (P.firstCovariantAdjointFiveHalfSection WQ U b) p (volume.restrict Y) := by
  apply memLp_of_compact_supported_continuousOn_majorant hY.measurableSet hS hSY
    (P.firstCovariantAdjointFiveHalfSection WQ U b)
    (P.firstCovariantAdjointFiveHalfSection_aestronglyMeasurable hY hd WF WQ U hU.contDiffOn b hw)
    (fun y hy hs => by simp only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,
      dif_pos hy,h0U y hs,map_zero])
    (fun y => firstAdjointFiveHalfCoordinateBudget d CG CK b y*‖U y‖)
    ((continuousOn_firstAdjointFiveHalfCoordinateBudget hY hΩ hSub hd hK b hw).mul hU.continuous.continuousOn.norm)
  intro y hy
  simp only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,dif_pos hy]
  exact ((P.firstCovariantCoordinateAdjointFiveHalfL (WQ y hy) b).le_opNorm (U y)).trans
    (mul_le_mul_of_nonneg_right
      (P.norm_firstCovariantCoordinateAdjointFiveHalfL_le_budget (WQ y hy) hCG hCK
        (hd.2.2.2.2.1.2 y hy).1.le b) (norm_nonneg _))

end ShrinkingSpheres
