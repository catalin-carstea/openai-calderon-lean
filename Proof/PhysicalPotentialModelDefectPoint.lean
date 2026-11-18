import Proof.PotentialModelDefectForm
import Proof.PhysicalFirstModelDefectPoint
import Proof.UniformPhysicalPotentialQuarticForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalPrincipalData.potentialModelDefectDensity {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) (W : PhysicalPotentialQuarticData P y CG CK) : ℝ :=
  metricDensity d.γ y*(
    P.potentialModelDefectRealForm W (fun p => (E.representative p).re)
      (Complex.reCLM.contDiff.comp E.representativeSmooth)+
    P.potentialModelDefectRealForm W (fun p => (E.representative p).im)
      (Complex.imCLM.contDiff.comp E.representativeSmooth))

theorem PhysicalPrincipalData.potentialModelDefectDensity_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG) (hBudget : physicalPotentialGeneratorBudget CF ≤ CG)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) :
    |P.potentialModelDefectDensity E y W| ≤
      (potentialModelDefectBudget K CF CG*(3*K^2+1))*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let CP := potentialModelDefectBudget K CF CG
  let CE := 3*K^2+1
  let Gr := fun p => (E.representative p).re
  let Gi := fun p => (E.representative p).im
  let hGr := Complex.reCLM.contDiff.comp E.representativeSmooth
  let hGi := Complex.imCLM.contDiff.comp E.representativeSmooth
  let Ur := ambientSobolevSection (3/2:ℝ) (by norm_num) Gr hGr
  let Ui := ambientSobolevSection (3/2:ℝ) (by norm_num) Gi hGi
  let Er := halfCovariantDirectionEnergy d Ur y (beta d.γ d.radius y) (axis 0)
  let Ei := halfCovariantDirectionEnergy d Ui y (beta d.γ d.radius y) (axis 0)
  let xr := P.potentialModelDefectRealForm W Gr hGr
  let xi := P.potentialModelDefectRealForm W Gi hGi
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hR := P.potential_model_defect_form_bound hd hK hf hε hε1 hy hCG hBudget W Gr hGr
  have hI := P.potential_model_defect_form_bound hd hK hf hε hε1 hy hCG hBudget W Gi hGi
  have hCP : 0 ≤ CP := potentialModelDefectBudget_nonneg K CF CG hK
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hβ : 0 ≤ beta d.γ d.radius y := Real.sqrt_nonneg _
  have hMR : beta d.γ d.radius y*‖Ur y‖^2 ≤ Er :=
    le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hβ) (sq_nonneg _))
  have hMI : beta d.γ d.radius y*‖Ui y‖^2 ≤ Ei :=
    le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hβ) (sq_nonneg _))
  have hr : |xr| ≤ CP*ε*Er := hR.trans (by
    have hh := mul_le_mul_of_nonneg_left hMR (mul_nonneg hCP hε)
    simpa only [mul_assoc,pow_two] using hh)
  have hi : |xi| ≤ CP*ε*Ei := hI.trans (by
    have hh := mul_le_mul_of_nonneg_left hMI (mul_nonneg hCP hε)
    simpa only [mul_assoc,pow_two] using hh)
  have hEnergy : metricDensity d.γ y*(Er+Ei) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y :=
    D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy 0
  have hh := two_weighted_scalar_forms_bound (metricDensity d.γ y) CP CE ε xr xi Er Ei
    (physicalEnergyDensity d.γ d.frame d.radius φ y) hμ hCP hε hr hi hEnergy
  simpa only [PhysicalPrincipalData.potentialModelDefectDensity,HarmonicTestExpansion.realSobolevSection,
    HarmonicTestExpansion.imagSobolevSection,xr,xi,Ur,Ui,Gr,Gi,hGr,hGi] using hh

end ShrinkingSpheres
