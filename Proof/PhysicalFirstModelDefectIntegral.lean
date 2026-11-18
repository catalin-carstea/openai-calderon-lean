import Proof.PhysicalFirstModelDefectPoint
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

lemma PhysicalPrincipalData.firstModelDefectDensity_contDiffOn
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (b : I) :
    ContDiffOn ℝ ∞ (P.firstModelDefectDensity E b) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hB : ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y :=
    (P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub hK b).sub ((hw b).smul contDiffOn_const)
  have hW (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) :
      ContDiffOn ℝ ∞ (fun x => highSectionCovariantDerivative d
        (ambientModelAdjointDefectSection d G hG) x (axis b)) Y := by
    simpa only [highSectionCovariantDerivativeLinear_apply] using
      (contDiffOn_highSectionCovariantDerivativeLinear hY d hg hK he _
        (contDiffOn_ambientModelAdjointDefectSection hY d G hG he hlog)).clm_apply
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X => axis b) Y)
  have hReal (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) :
      ContDiffOn ℝ ∞ (firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) G hG b) Y :=
    ((sphereSobolevInclusionL 2 0 (by norm_num)).contDiff.comp_contDiffOn
      (contDiff_ambientSobolevSection 2 (by norm_num) G hG).contDiffOn).inner ℝ (hB.clm_apply (hW G hG))
  exact (hg.contDiffOn_density hK).mul
    ((hReal _ (Complex.reCLM.contDiff.comp E.representativeSmooth)).add
      (hReal _ (Complex.imCLM.contDiff.comp E.representativeSmooth)))

theorem uniform_physical_first_model_defect_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ b : I,
      IntegrableOn (P.firstModelDefectDensity E b) Y ∧
        |∫ y in Y,P.firstModelDefectDensity E b y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,C,hη,hη1,hC,hPoint⟩ := uniform_physical_first_model_defect_point_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd CT P φ E D hφ b
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hSmooth := P.firstModelDefectDensity_contDiffOn hY hΩ hSub hd hKpos
    (fun b => (hWeight floor hf ε hε (hSmall.trans hη1) d hd b).1) E b
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖P.firstModelDefectDensity E b y‖ ≤
      (C*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint floor hf ε hε hSmall d hd CT P φ E D hφ b y hy
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ).const_mul (C*ε)
  refine ⟨hDom.mono' (hSmooth.continuousOn.aestronglyMeasurable hY.measurableSet) hBound,?_⟩
  have ht := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using ht

end ShrinkingSpheres
