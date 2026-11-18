import Proof.PhysicalPotentialCoreOperatorBounds
import Proof.CompactSupportedChosenOperatorLp
import Proof.CompactSupportedLpWeightedSquare

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

lemma potentialQuadraticCoreSection_memLp (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (p : ℝ≥0∞) :
    MemLp (P.potentialQuadraticCoreSection W U) p (volume.restrict Y) := by
  exact memLp_chosen_operator_section_of_continuous_majorant hY.measurableSet hS hSY
    (fun y hy => P.potentialQuadraticCoreL (W y hy)) U hU h0U
    (P.potentialQuadraticCoreSection_aestronglyMeasurable hY hSub hd hK W U hU)
    (fun y => (physicalPotentialGeneratorBudget CF*(3*physicalPotentialGeneratorBudget CF+CK))*potentialWordMass d y)
    (continuousOn_const.mul (continuousOn_potentialWordMass hY hSub hd hK))
    (fun y hy => P.norm_potentialQuadraticCoreL_le_word_mass hy (W y hy) hCK (hd.2.2.2.2.1.2 y hy).1.le) p

lemma potentialQuadraticAdjointCoreSection_memLp (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (p : ℝ≥0∞) :
    MemLp (P.potentialQuadraticAdjointCoreSection W U) p (volume.restrict Y) := by
  exact memLp_chosen_operator_section_of_continuous_majorant hY.measurableSet hS hSY
    (fun y hy => P.potentialQuadraticAdjointCoreL (W y hy)) U hU h0U
    (P.potentialQuadraticAdjointCoreSection_aestronglyMeasurable hY hSub hd hK W U hU)
    (fun y => (CG*(3*CG+CK))*potentialWordMass d y)
    (continuousOn_const.mul (continuousOn_potentialWordMass hY hSub hd hK))
    (fun y hy => P.norm_potentialQuadraticAdjointCoreL_le_word_mass (W y hy) hCG hCK (hd.2.2.2.2.1.2 y hy).1.le) p

lemma potentialQuadraticCoreSection_zero_of_source_zero (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (U : X → SphereSobolev (5/2:ℝ))
    {y : X} (hU : U y=0) : P.potentialQuadraticCoreSection W U y=0 :=
  chosenOperatorSection_eq_zero_of_source_eq_zero (fun y hy => P.potentialQuadraticCoreL (W y hy)) U hU

lemma potentialQuadraticAdjointCoreSection_zero_of_source_zero (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (U : X → SphereSobolev (5/2:ℝ))
    {y : X} (hU : U y=0) : P.potentialQuadraticAdjointCoreSection W U y=0 :=
  chosenOperatorSection_eq_zero_of_source_eq_zero (fun y hy => P.potentialQuadraticAdjointCoreL (W y hy)) U hU

/-- Both actual potential outputs have individual physical square
integrability. Integrability of their norm difference alone is not used
as a substitute for either domain statement. -/
theorem potentialCoreOperators_weighted_square_integrable (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    IntegrableOn (fun y => metricDensity d.γ y*‖P.potentialQuadraticCoreSection W U y‖^2) Y ∧
      IntegrableOn (fun y => metricDensity d.γ y*‖P.potentialQuadraticAdjointCoreSection W U y‖^2) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  refine ⟨integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _
    (P.potentialQuadraticCoreSection_memLp hY hSub hd hK W hCK U hU S hS hSY h0U 2)
    (fun _ _ hs => P.potentialQuadraticCoreSection_zero_of_source_zero W U (h0U _ hs)) _
    (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _),
    integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _
    (P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY h0U 2)
    (fun _ _ hs => P.potentialQuadraticAdjointCoreSection_zero_of_source_zero W U (h0U _ hs)) _
    (hg.contDiffOn_density hK).continuousOn (fun _ _ => Real.sqrt_nonneg _)⟩

end PhysicalPrincipalData
end ShrinkingSpheres
