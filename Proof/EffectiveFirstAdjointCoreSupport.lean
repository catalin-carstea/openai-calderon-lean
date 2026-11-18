import Proof.EffectiveFirstAdjointDensityCore
import Proof.LocalMixedOperatorGreen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms

/-- The observable LOW representative has a genuine global supported
smooth realization, even when the selected HIGH representative has only
proved measurability. -/
lemma PhysicalFirstCommutatorPacket.covariantAdjointLowSection_supported
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    {P : PhysicalPrincipalData Y d CF CT} (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    ContDiff ℝ ∞ (WF.covariantAdjointLowSection U b) ∧
      ∀ x ∉ S,WF.covariantAdjointLowSection U b x=0 := by
  let L := fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  have hL : ContDiff ℝ ∞ L := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU
  have h0L (y) (hy : y ∉ S) : L y=0 := by simp only [L,h0U y hy,map_zero]
  refine ⟨contDiff_supported_operator_apply L (WF.covariantCoordinateAdjointHigher b) S hS hL h0L
    (fun y hy => (WF.covariantCoordinateAdjointHigher_smooth hd b hw).contDiffAt (hY.mem_nhds (hSY hy))),?_⟩
  intro y hy
  change WF.covariantCoordinateAdjointHigher b y (L y)=0
  rw [h0L y hy,map_zero]

lemma PhysicalPrincipalData.firstAdjointDensityCoreRow_zero_off
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) {y : X} (hy : y ∉ S) :
    P.firstAdjointDensityCoreRow WF WQ U b y=0 := by
  have hZ := WF.covariantAdjointLowSection_supported hY hd U hU S hS hSY h0U b hw
  have hDZ := directional_eq_zero_off (WF.covariantAdjointLowSection U b) S hS hZ.2 (axis b) y hy
  have hDZ' : fderiv ℝ (WF.covariantAdjointLowSection U b) y (axis b)=0 := hDZ
  have hTop : P.firstCovariantAdjointFiveHalfSection WQ U b y=0 := by
    by_cases h : y ∈ Y
    · simp only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,dite_eq_left h,h0U y hy,map_zero]
    · simp only [PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection,dite_eq_right h]
  simp only [PhysicalPrincipalData.firstAdjointDensityCoreRow,hDZ',hZ.2 y hy,hTop,map_zero,
    smul_zero,sub_self,add_zero]

end ShrinkingSpheres
