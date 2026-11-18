import Proof.ParallelEnergySectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set MeasureTheory
open scoped ContDiff
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual paired first-self density is integrable on every genuine
compactly supported common core. No energy comparison is asserted here. -/
theorem firstSelfDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (firstSelfDensity P WF W U) Y := by
  have hV : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h0V (x) (hx : x ∉ S) : fiveHalfToTwoSection U x=0 := by
    simp only [fiveHalfToTwoSection,h0U x hx,map_zero]
  have hSquares := P.firstCoreOperators_weighted_square_integrable hY hΩ hSub hd hK
    WF W hCG hCK U (fiveHalfToTwoSection U) hU hV S hS hSY h0U h0V
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK)
  unfold firstSelfDensity
  simp_rw [mul_sub]
  exact hSquares.1.sub hSquares.2

/-- Integrability for the exact real-plus-imaginary sector used by the
physical norm comparison, retaining the already selected packet. -/
theorem firstSelfComplexDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    IntegrableOn (firstSelfComplexDensity P WF W E) Y := by
  exact (firstSelfDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)) E.supportSet E.compactSupportSet
    E.supportSubset (fun x hx => E.realHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)).add
    (firstSelfDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)) E.supportSet E.compactSupportSet
    E.supportSubset (fun x hx => E.imagHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx))

end ShrinkingSpheres.ParallelEnergy
