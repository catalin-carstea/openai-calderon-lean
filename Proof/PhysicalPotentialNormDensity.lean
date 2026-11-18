import Proof.PhysicalPotentialActualNorm
import Proof.PhysicalErrorForms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma physicalEnergyDensity_mass_le (d : Data) (φ : Field) (y : X) :
    metricDensity d.γ y*beta d.γ d.radius y*sobolevSq d.γ d.frame (3/2:ℝ) y (fun w => φ (y,w)) ≤
      physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hH : 0 ≤ ∑ i : I,fiberSq d.frame y (fun w => horizontal d.γ φ y w (d.frame y i)) :=
    Finset.sum_nonneg (fun _ _ => fiberSq_nonneg _ _ _)
  have hM : 0 ≤ (beta d.γ d.radius y)^2*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w)) :=
    mul_nonneg (sq_nonneg _) (sobolevSq_nonneg _ _ _ _ _)
  have hHs : 0 ≤ (beta d.γ d.radius y)⁻¹*
      ∑ i : I,sobolevSq d.γ d.frame (1/2:ℝ) y (fun w => horizontal d.γ φ y w (d.frame y i)) :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Finset.sum_nonneg (fun _ _ => sobolevSq_nonneg _ _ _ _ _))
  have hInside := le_add_of_nonneg_left (a:=beta d.γ d.radius y*sobolevSq d.γ d.frame (3/2:ℝ) y (fun w => φ (y,w))) (add_nonneg (add_nonneg hH hM) hHs)
  exact (by simpa only [physicalEnergyDensity,mul_assoc] using
    mul_le_mul_of_nonneg_left hInside (show 0 ≤ metricDensity d.γ y from Real.sqrt_nonneg _))

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def potentialQuadraticNormDensity (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} {CG CK : ℝ}
    (W : PhysicalPotentialQuarticData P y CG CK) : ℝ :=
  let Ur := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).re)
    (Complex.reCLM.contDiff.comp E.representativeSmooth) y
  let Ui := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).im)
    (Complex.imCLM.contDiff.comp E.representativeSmooth) y
  metricDensity d.γ y*((‖P.potentialQuadraticCoreL W Ur‖^2-‖P.potentialQuadraticAdjointCoreL W Ur‖^2)+
    (‖P.potentialQuadraticCoreL W Ui‖^2-‖P.potentialQuadraticAdjointCoreL W Ui‖^2))

lemma abs_potentialQuadraticNormDensity_le (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Y) {CG CK CE ε : ℝ} (W : PhysicalPotentialQuarticData P y CG CK)
    (hCE : 0 ≤ CE) (hε : 0 ≤ ε)
    (hNorm : ∀ u : SphereSobolev (5/2:ℝ),
      |‖P.potentialQuadraticCoreL W u‖^2-‖P.potentialQuadraticAdjointCoreL W u‖^2| ≤
        CE*ε*beta d.γ d.radius y*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u‖^2) :
    |P.potentialQuadraticNormDensity E W| ≤ CE*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let Ur := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).re)
    (Complex.reCLM.contDiff.comp E.representativeSmooth) y
  let Ui := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) (fun p => (E.representative p).im)
    (Complex.imCLM.contDiff.comp E.representativeSmooth) y
  let R := ‖P.potentialQuadraticCoreL W Ur‖^2-‖P.potentialQuadraticAdjointCoreL W Ur‖^2
  let I := ‖P.potentialQuadraticCoreL W Ui‖^2-‖P.potentialQuadraticAdjointCoreL W Ui‖^2
  have hUr : sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) Ur=
      E.realSobolevSection (3/2:ℝ) (by norm_num) y :=
    ambientHigherSobolevSection_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num) _ _ y
  have hUi : sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) Ui=
      E.imagSobolevSection (3/2:ℝ) (by norm_num) y :=
    ambientHigherSobolevSection_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num) _ _ y
  have hR : |R| ≤ CE*ε*beta d.γ d.radius y*‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2 := by
    simpa only [hUr] using hNorm Ur
  have hI : |I| ≤ CE*ε*beta d.γ d.radius y*‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2 := by
    simpa only [hUi] using hNorm Ui
  have hSum := (abs_add_le R I).trans (add_le_add hR hI)
  have hMass := E.sobolev_eq_native_sections hFrame (3/2:ℝ) (by norm_num) hy
  change |metricDensity d.γ y*(R+I)| ≤ _
  rw [abs_mul,abs_of_nonneg (show 0 ≤ metricDensity d.γ y from Real.sqrt_nonneg _)]
  calc
    _ ≤ metricDensity d.γ y*(CE*ε*beta d.γ d.radius y*
        (‖E.realSobolevSection (3/2:ℝ) (by norm_num) y‖^2+
          ‖E.imagSobolevSection (3/2:ℝ) (by norm_num) y‖^2)) :=
      mul_le_mul_of_nonneg_left (hSum.trans_eq (by ring)) (Real.sqrt_nonneg _)
    _ = CE*ε*(metricDensity d.γ y*beta d.γ d.radius y*
        sobolevSq d.γ d.frame (3/2:ℝ) y (fun w => φ (y,w))) := by rw [hMass];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (physicalEnergyDensity_mass_le d φ y) (mul_nonneg hCE hε)
end PhysicalPrincipalData
end ShrinkingSpheres
