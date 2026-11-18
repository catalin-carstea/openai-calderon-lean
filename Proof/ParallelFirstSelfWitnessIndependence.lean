import Proof.ParallelFirstSelfIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine inclusion injectivity identifies the true-adjoint higher
coefficient of any two coherent packets for the same physical data. -/
lemma covariantCoordinateAdjointHigher_eq
    {Y : Set X} {d : Data} {CF CT CB CS CB' CS' ε : ℝ}
    {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WF' : PhysicalFirstCommutatorPacket P CB' CS' ε) (b : I) {y : X} (hy : y ∈ Y) :
    WF.covariantCoordinateAdjointHigher b y=WF'.covariantCoordinateAdjointHigher b y := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  exact DFunLike.congr_fun ((WF.covariantCoordinateAdjointHigher_balanced b hy).trans
    (WF'.covariantCoordinateAdjointHigher_balanced b hy).symm) u

/-- The actual density core is independent of both endpoint witness
packages. Its weak covariant divergence uniquely determines its value. -/
lemma firstAdjointDensityCoreRow_eq
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CB' CS' CG' CK' : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (WF' : PhysicalFirstCommutatorPacket P CB' CS' ε)
    (W' : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG' CK')
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    (b : I) {y : X} (hy : y ∈ Y) :
    P.firstAdjointDensityCoreRow WF W U b y=P.firstAdjointDensityCoreRow WF' W' U b y := by
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  rw [P.firstAdjointDensityCoreRow_balanced_graph hY hΩ hd hK WF W U hU b hw hy,
    P.firstAdjointDensityCoreRow_balanced_graph hY hΩ hd hK WF' W' U hU b hw hy]
  unfold PhysicalPrincipalData.firstAdjointBalancedDensityRow
    PhysicalFirstCommutatorPacket.covariantCoordinateAdjointDerivative halfOperatorCovariantDerivativeL
  rw [covariantCoordinateAdjointHigher_eq WF WF' b hy]

/-- The physical first formal-adjoint output is intrinsic on the common
core, even when the quantitative witness constants differ. -/
lemma firstFormalAdjointCore_eq
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CB' CS' CG' CK' : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (WF' : PhysicalFirstCommutatorPacket P CB' CS' ε)
    (W' : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG' CK')
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) :
    P.firstFormalAdjointCore WF W U y=P.firstFormalAdjointCore WF' W' U y := by
  unfold PhysicalPrincipalData.firstFormalAdjointCore PhysicalPrincipalData.firstFormalAdjointCoreRow
  apply Finset.sum_congr rfl
  intro b _
  rw [firstAdjointDensityCoreRow_eq hY hΩ hSub hd hK P WF W WF' W' U hU b hy]

lemma firstSelfDensity_eq
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CB' CS' CG' CK' : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (WF' : PhysicalFirstCommutatorPacket P CB' CS' ε)
    (W' : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG' CK')
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) :
    firstSelfDensity P WF W U y=firstSelfDensity P WF' W' U y := by
  unfold firstSelfDensity
  rw [firstFormalAdjointCore_eq hY hΩ hSub hd hK P WF W WF' W' U hU hy]

/-- The exact complex density is likewise independent of quantitative witnesses. -/
lemma firstSelfComplexDensity_eq
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CB' CS' CG' CK' : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (WF' : PhysicalFirstCommutatorPacket P CB' CS' ε)
    (W' : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG' CK')
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) :
    firstSelfComplexDensity P WF W E y=firstSelfComplexDensity P WF' W' E y := by
  unfold firstSelfComplexDensity
  rw [firstSelfDensity_eq hY hΩ hSub hd hK P WF W WF' W' _
      (E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)).contDiffOn hy,
    firstSelfDensity_eq hY hΩ hSub hd hK P WF W WF' W' _
      (E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)).contDiffOn hy]

/-- The companion mixed sector can also retain its arbitrary supplied
witnesses after any proof using a convenient coherent packet. -/
lemma scalarFirstComplexDensity_eq
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK CB' CS' CG' CK' : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (WF' : PhysicalFirstCommutatorPacket P CB' CS' ε)
    (W' : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG' CK')
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) :
    scalarFirstComplexDensity P WF W E y=scalarFirstComplexDensity P WF' W' E y := by
  unfold scalarFirstComplexDensity scalarFirstDensity
  rw [firstFormalAdjointCore_eq hY hΩ hSub hd hK P WF W WF' W' _
      (E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)).contDiffOn hy,
    firstFormalAdjointCore_eq hY hΩ hSub hd hK P WF W WF' W' _
      (E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)).contDiffOn hy]

end ShrinkingSpheres.ParallelEnergy
