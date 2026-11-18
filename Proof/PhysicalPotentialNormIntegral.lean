import Proof.PhysicalPotentialCoreMeasurability
import Proof.PhysicalPotentialNormDensity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

def potentialQuadraticNormDensityFamily (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) : X → ℝ := by
  classical
  exact fun y => if hy : y ∈ Y then P.potentialQuadraticNormDensity E (W y hy) else 0

lemma potentialQuadraticNormDensityFamily_aestronglyMeasurable {Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    AEStronglyMeasurable (P.potentialQuadraticNormDensityFamily E W) (volume.restrict Y) := by
  let Ur := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).re)
    (Complex.reCLM.contDiff.comp E.representativeSmooth)
  let Ui := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).im)
    (Complex.imCLM.contDiff.comp E.representativeSmooth)
  have hr := contDiff_ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).re)
    (Complex.reCLM.contDiff.comp E.representativeSmooth)
  have hi := contDiff_ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).im)
    (Complex.imCLM.contDiff.comp E.representativeSmooth)
  have hFr := P.potentialQuadraticCoreSection_aestronglyMeasurable hY hSub hd hK W Ur hr
  have hBr := P.potentialQuadraticAdjointCoreSection_aestronglyMeasurable hY hSub hd hK W Ur hr
  have hFi := P.potentialQuadraticCoreSection_aestronglyMeasurable hY hSub hd hK W Ui hi
  have hBi := P.potentialQuadraticAdjointCoreSection_aestronglyMeasurable hY hSub hd hK W Ui hi
  have hμ : AEStronglyMeasurable (metricDensity d.γ) (volume.restrict Y) := ((hd.1.1.contDiffOn_density hK).mono hSub).continuousOn.aestronglyMeasurable hY.measurableSet
  have hForm := hμ.mul (((hFr.norm.mul hFr.norm).sub (hBr.norm.mul hBr.norm)).add
    ((hFi.norm.mul hFi.norm).sub (hBi.norm.mul hBi.norm)))
  apply hForm.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  simp only [Pi.mul_apply,Pi.sub_apply,Pi.add_apply,potentialQuadraticNormDensityFamily,potentialQuadraticNormDensity,
    potentialQuadraticCoreSection,potentialQuadraticAdjointCoreSection,dite_eq_left hy,Ur,Ui,pow_two]

/-- The full genuine quadratic potential norm density is integrable and
bounded in the SAME frozen physical energy. No measurability or regularity
premise on pointwise chosen higher adjoints is assumed. -/
lemma integral_potentialQuadraticNormDensity_bound {Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε CE : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hCE : 0 ≤ CE) (hε : 0 ≤ ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (hφ : Test Y d.γ d.frame φ)
    (hBound : ∀ (y : X) (hy : y ∈ Y),|P.potentialQuadraticNormDensity E (W y hy)| ≤
      CE*ε*physicalEnergyDensity d.γ d.frame d.radius φ y) :
    IntegrableOn (P.potentialQuadraticNormDensityFamily E W) Y ∧
      |∫ y in Y,P.potentialQuadraticNormDensityFamily E W y| ≤ CE*ε*energySq Y d.γ d.frame d.radius φ := by
  have hK0 := zero_lt_one.trans_le hK
  have hMeas := P.potentialQuadraticNormDensityFamily_aestronglyMeasurable hY hSub hd hK0 W E
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame := fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hK0 d.frame he hFrame hf hφ).const_mul (CE*ε)
  have hB : ∀ᵐ y ∂volume.restrict Y,‖P.potentialQuadraticNormDensityFamily E W y‖ ≤
      CE*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs,potentialQuadraticNormDensityFamily,dite_eq_left hy]
    exact hBound y hy
  refine ⟨hDom.mono' hMeas hB,?_⟩
  have h := norm_integral_le_of_norm_le hDom hB
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using h
end PhysicalPrincipalData
end ShrinkingSpheres
