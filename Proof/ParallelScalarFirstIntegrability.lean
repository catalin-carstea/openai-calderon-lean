import Proof.ParallelEnergySectors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both orientations of the actual scalar/complete-first cross form are
integrable on the genuine common supported core. No estimate of either
orientation separately is asserted. -/
theorem scalarFirstDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (scalarFirstDensity P WF W U) Y := by
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have h0U2 (x : X) (hx : x ∉ S) : fiveHalfToTwoSection U x=0 := by
    simp only [fiveHalfToTwoSection,h0U x hx,map_zero]
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hScalar := physical_scalar_principal_core_memLp hY hSub hd hK _ hU2 S hS hSY h0U2 2
  have hScalar0 := physical_scalar_principal_core_supported hY hSub hd hK _ hU2 S hS.isClosed hSY h0U2
  have hFirst := P.firstCovariantCoreSection_memLp hY hΩ hSub hd hK _ hU2 S hS hSY h0U2 hw 2
  have hAdjoint := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U hw 2
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hForward := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _
    hScalar.1 hFirst (fun y _ hy => hScalar0.1.2 y hy) _ (hg.contDiffOn_density hK).continuousOn
  have hBackward := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _
    hScalar.2 hAdjoint (fun y _ hy => hScalar0.2.2 y hy) _ (hg.contDiffOn_density hK).continuousOn
  have hDifference := (hForward.sub hBackward).const_mul 2
  apply hDifference.congr
  exact Filter.Eventually.of_forall (fun y => by
    simp only [scalarFirstDensity,Pi.sub_apply]
    ring)

/-- Qualitative integrability of the exact selected complex paired sector,
for any already selected principal, commutator and potential packets. -/
theorem scalarFirstComplexDensity_integrableOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    IntegrableOn (scalarFirstComplexDensity P WF W E) Y := by
  have hReal := scalarFirstDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num))
    E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)
  have hImag := scalarFirstDensity_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)
  exact hReal.add hImag

end ShrinkingSpheres.ParallelEnergy
