import Proof.PhysicalTruncatedCoreAdjunction
import Proof.PhysicalPotentialActualSquares

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

structure PhysicalTruncatedCoreCalculus {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) : Prop where
  balanced : ∀ (U : X → SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ U → ∀ y ∈ Y,
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.truncatedCovariantCoreSection W U y)=
      P.truncatedResidualValue (fiveHalfToTwoSection U) y
  domain : ∀ (U : X → SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ U →
    ∀ S : Set X,IsCompact S → S ⊆ Y → (∀ x ∉ S,U x=0) → ∀ p : ℝ≥0∞,
      MemLp (P.truncatedCovariantCoreSection W U) p (volume.restrict Y) ∧
        MemLp (P.truncatedFormalAdjointCore WF W U) p (volume.restrict Y)
  physicalSquares : ∀ (U : X → SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ U →
    ∀ S : Set X,IsCompact S → S ⊆ Y → (∀ x ∉ S,U x=0) →
      IntegrableOn (fun y => metricDensity d.γ y*‖P.truncatedCovariantCoreSection W U y‖^2) Y ∧
        IntegrableOn (fun y => metricDensity d.γ y*‖P.truncatedFormalAdjointCore WF W U y‖^2) Y
  adjunction : ∀ (U V : X → SphereSobolev (5/2:ℝ)),ContDiff ℝ ∞ U → ContDiff ℝ ∞ V →
    ∀ S : Set X,IsCompact S → S ⊆ Y → (∀ x ∉ S,U x=0) → (∀ x ∉ S,V x=0) →
      IntegrableOn (fun y => metricDensity d.γ y*
        ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.truncatedCovariantCoreSection W V y⟫_ℝ) Y ∧
      IntegrableOn (fun y => metricDensity d.γ y*
        ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y),P.truncatedFormalAdjointCore WF W U y⟫_ℝ) Y ∧
      (∫ y in Y,metricDensity d.γ y*
        ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.truncatedCovariantCoreSection W V y⟫_ℝ)=
        (∫ y in Y,metricDensity d.γ y*
          ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (V y),P.truncatedFormalAdjointCore WF W U y⟫_ℝ)

theorem physical_truncated_core_calculus
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    PhysicalTruncatedCoreCalculus P WF W where
  balanced := fun U hU _ hy => P.truncatedCovariantCoreSection_balanced hY hΩ hd hK W U hU hy
  domain := fun U hU S hS hSY h0U p => P.truncatedCoreOperators_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U p
  physicalSquares := fun U hU S hS hSY h0U =>
    P.truncatedCoreOperators_weighted_square_integrable hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY h0U
  adjunction := fun U V hU hV S hS hSY h0U h0V =>
    P.truncatedCoreOperators_green hY hΩ hSub hd hK WF W hCG hCK U V hU hV S hS hSY h0U h0V

/-- All genuine common-domain and adjunction witnesses for the actual
complete truncated residual are selected uniformly before every test.
The potential square comparison uses the same selected potential family. -/
theorem uniform_physical_truncated_core_calculus {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS CG CK CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∃ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      PhysicalTruncatedCoreCalculus P WF W ∧
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,Test Y d.γ d.frame φ →
        IntegrableOn (P.potentialForwardSquareDensityFamily E W) Y ∧
        IntegrableOn (P.potentialAdjointSquareDensityFamily E W) Y ∧
        |(∫ y in Y,P.potentialForwardSquareDensityFamily E W y)-
          (∫ y in Y,P.potentialAdjointSquareDensityFamily E W y)| ≤ CE*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηF,CB,CS,hηF,hηF1,hCB,hCS,hFirst⟩ :=
    uniform_physical_first_commutator_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηQ,CG,CK,CE,hηQ,hηQ1,hCG,hCK,hCE,hPotential⟩ :=
    uniform_physical_potential_actual_square_comparison hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨min ηF ηQ,CB,CS,CG,CK,CE,lt_min hηF hηQ,(min_le_left _ _).trans hηF1,hCB,hCS,hCG,hCK,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨WF⟩ := hFirst floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  obtain ⟨W,hW⟩ := hPotential floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CT P
  have hCalc : PhysicalTruncatedCoreCalculus P WF W :=
    physical_truncated_core_calculus P hY hΩ hSub hd (zero_lt_one.trans_le hK) WF W hCG hCK
  exact ⟨WF,W,hCalc,hW⟩

end ShrinkingSpheres
