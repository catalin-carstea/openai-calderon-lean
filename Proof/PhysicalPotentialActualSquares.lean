import Proof.PhysicalPotentialCoreAdjunctionIntegral
import Proof.HarmonicHigherTestSections
import Proof.UniformPhysicalPotentialNormIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

def potentialForwardSquareDensityFamily (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (y : X) : ℝ :=
  metricDensity d.γ y*(‖P.potentialQuadraticCoreSection W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2+
    ‖P.potentialQuadraticCoreSection W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)

def potentialAdjointSquareDensityFamily (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (y : X) : ℝ :=
  metricDensity d.γ y*(‖P.potentialQuadraticAdjointCoreSection W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2+
    ‖P.potentialQuadraticAdjointCoreSection W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)

lemma potentialNormDensityFamily_eq_sub (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) {y : X} (hy : y ∈ Y) :
    P.potentialQuadraticNormDensityFamily E W y=
      P.potentialForwardSquareDensityFamily E W y-P.potentialAdjointSquareDensityFamily E W y := by
  simp only [potentialQuadraticNormDensityFamily,potentialQuadraticNormDensity,potentialForwardSquareDensityFamily,
    potentialAdjointSquareDensityFamily,potentialQuadraticCoreSection,potentialQuadraticAdjointCoreSection,
    HarmonicTestExpansion.realHigherSobolevSection,HarmonicTestExpansion.imagHigherSobolevSection,dite_eq_left hy]
  ring

lemma potentialCoreSquareDensities_integrable {Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    IntegrableOn (P.potentialForwardSquareDensityFamily E W) Y ∧
      IntegrableOn (P.potentialAdjointSquareDensityFamily E W) Y := by
  have hR := P.potentialCoreOperators_weighted_square_integrable hY hSub hd hK W hCG hCK
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset (fun _ hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hI := P.potentialCoreOperators_weighted_square_integrable hY hSub hd hK W hCG hCK
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset (fun _ hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  constructor
  · unfold potentialForwardSquareDensityFamily
    simp only [mul_add]
    exact hR.1.add hI.1
  · unfold potentialAdjointSquareDensityFamily
    simp only [mul_add]
    exact hR.2.add hI.2

end PhysicalPrincipalData

/-- The complete potential comparison as a difference of two separately
defined physical squared norms, with the SAME higher family selected
before every test field. -/
theorem uniform_physical_potential_actual_square_comparison {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CG CK CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,Test Y d.γ d.frame φ →
        IntegrableOn (P.potentialForwardSquareDensityFamily E W) Y ∧
        IntegrableOn (P.potentialAdjointSquareDensityFamily E W) Y ∧
        |(∫ y in Y,P.potentialForwardSquareDensityFamily E W y)-
          (∫ y in Y,P.potentialAdjointSquareDensityFamily E W y)| ≤ CE*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,hProduce⟩ :=
    uniform_physical_potential_quadratic_norm_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨η,CG,CK,CE,hη,hη1,hCG,hCK,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W,hW⟩ := hProduce floor hf ε hε hSmall d hd CT P
  refine ⟨W,?_⟩
  intro φ E hφ
  have hSquares := P.potentialCoreSquareDensities_integrable hY hSub hd (zero_lt_one.trans_le hK) W hCG hCK E
  refine ⟨hSquares.1,hSquares.2,?_⟩
  have hEq : (∫ y in Y,P.potentialQuadraticNormDensityFamily E W y)=
      (∫ y in Y,P.potentialForwardSquareDensityFamily E W y)-
        (∫ y in Y,P.potentialAdjointSquareDensityFamily E W y) := by
    calc
      _ = ∫ y in Y,P.potentialForwardSquareDensityFamily E W y-P.potentialAdjointSquareDensityFamily E W y :=
        integral_congr_ae (by
          filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
          exact P.potentialNormDensityFamily_eq_sub E W hy)
      _ = _ := integral_sub hSquares.1 hSquares.2
  rw [←hEq]
  exact (hW φ E hφ).2

end ShrinkingSpheres
