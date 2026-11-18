import Proof.PhysicalPotentialModelDefectPoint
import Proof.PhysicalPotentialCoreMeasurability
import Proof.SmoothEnergyRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalPrincipalData.potentialModelDefectDensityFamily {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) : X → ℝ := by
  classical
  exact fun y => if hy : y ∈ Y then P.potentialModelDefectDensity E y (W y hy) else 0

lemma PhysicalPrincipalData.potentialModelDefectDensityFamily_aestronglyMeasurable
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) :
    AEStronglyMeasurable (P.potentialModelDefectDensityFamily E W) (volume.restrict Y) := by
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  let Zr := ambientModelDefectFiveHalfSection d (fun p => (E.representative p).re)
    (Complex.reCLM.contDiff.comp E.representativeSmooth)
  let Zi := ambientModelDefectFiveHalfSection d (fun p => (E.representative p).im)
    (Complex.imCLM.contDiff.comp E.representativeSmooth)
  have hZR : ContDiff ℝ ∞ Zr := (contDiff_supported_ambientModelDefectFiveHalfSection hY d _ _
    hlog he E.supportSet E.compactSupportSet.isClosed E.supportSubset
    (fun x hx => E.realSobolevSection_zero 2 (by norm_num) hx)).1
  have hZI : ContDiff ℝ ∞ Zi := (contDiff_supported_ambientModelDefectFiveHalfSection hY d _ _
    hlog he E.supportSet E.compactSupportSet.isClosed E.supportSubset
    (fun x hx => E.imagSobolevSection_zero 2 (by norm_num) hx)).1
  have hPr := P.potentialQuadraticCoreSection_aestronglyMeasurable hY hSub hd hK W Zr hZR
  have hPi := P.potentialQuadraticCoreSection_aestronglyMeasurable hY hSub hd hK W Zi hZI
  have hUr := ((sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)).contDiff.comp
    (E.contDiff_realSobolevSection (3/2:ℝ) (by norm_num))).continuous.aestronglyMeasurable
      (μ:=volume.restrict Y)
  have hUi := ((sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)).contDiff.comp
    (E.contDiff_imagSobolevSection (3/2:ℝ) (by norm_num))).continuous.aestronglyMeasurable
      (μ:=volume.restrict Y)
  have hμ : AEStronglyMeasurable (metricDensity d.γ) (volume.restrict Y) :=
    ((hd.1.1.contDiffOn_density hK).mono hSub).continuousOn.aestronglyMeasurable hY.measurableSet
  have hh := hμ.mul ((hUr.inner hPr).add (hUi.inner hPi))
  apply hh.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  simp only [PhysicalPrincipalData.potentialModelDefectDensityFamily,
    PhysicalPrincipalData.potentialModelDefectDensity,PhysicalPrincipalData.potentialModelDefectRealForm,
    PhysicalPrincipalData.potentialQuadraticCoreSection,HarmonicTestExpansion.realSobolevSection,
    HarmonicTestExpansion.imagSobolevSection,dite_eq_left hy,Zr,Zi,Pi.mul_apply,Pi.add_apply,Function.comp_apply]

theorem uniform_physical_potential_model_defect_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CG CK C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CK ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      IntegrableOn (P.potentialModelDefectDensityFamily E W) Y ∧
        |∫ y in Y,P.potentialModelDefectDensityFamily E W y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  classical
  obtain ⟨η,CG,CK,C0,hη,hη1,hCG,hCK,hC0,hBudget,hData⟩ :=
    uniform_physical_potential_quartic_weak_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  let C := potentialModelDefectBudget K CF CG*(3*K^2+1)
  have hC : 0 ≤ C := mul_nonneg (potentialModelDefectBudget_nonneg K CF CG hK) (by positivity)
  refine ⟨η,CG,CK,C,hη,hη1,hCG,hCK,hC,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  choose W hW using hData floor hf ε hε hSmall d hd CT P
  refine ⟨W,?_⟩
  intro φ E D hφ
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hMeas := P.potentialModelDefectDensityFamily_aestronglyMeasurable hY hSub hd hKpos E W
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖P.potentialModelDefectDensityFamily E W y‖ ≤
      (C*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs,PhysicalPrincipalData.potentialModelDefectDensityFamily,dif_pos hy]
    exact P.potentialModelDefectDensity_bound hY hSub hd hK hf hε (hSmall.trans hη1) hCG hBudget E D hφ hy (W y hy)
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ).const_mul (C*ε)
  refine ⟨hDom.mono' hMeas hBound,?_⟩
  have ht := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using ht

end ShrinkingSpheres
