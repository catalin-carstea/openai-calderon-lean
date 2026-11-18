import Proof.CanonicalFirstModelDefectPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma two_weighted_scalar_forms_bound (mu CP CE ε xr xi Er Ei energy : ℝ)
    (hmu : 0 ≤ mu) (hCP : 0 ≤ CP) (hε : 0 ≤ ε)
    (hr : |xr| ≤ CP*ε*Er) (hi : |xi| ≤ CP*ε*Ei)
    (he : mu*(Er+Ei) ≤ CE*energy) :
    |mu*(xr+xi)| ≤ (CP*CE)*ε*energy := by
  rw [abs_mul,abs_of_nonneg hmu]
  calc
    _ ≤ mu*(CP*ε*Er+CP*ε*Ei) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hr hi)) hmu
    _ = (CP*ε)*(mu*(Er+Ei)) := by ring
    _ ≤ (CP*ε)*(CE*energy) := mul_le_mul_of_nonneg_left he (mul_nonneg hCP hε)
    _ = _ := by ring

def PhysicalPrincipalData.firstModelDefectDensity {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (b : I) (y : X) : ℝ :=
  metricDensity d.γ y*(
    firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b)
      (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth) b y+
    firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b)
      (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth) b y)

theorem uniform_physical_first_model_defect_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ b : I,∀ y ∈ Y,
      |P.firstModelDefectDensity E b y| ≤ C*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  obtain ⟨η,CA,hη,hη1,hCA,hAdjoint⟩ := uniform_first_covariant_coordinate_adjoint_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  let CP := firstModelDefectBudget K (Cj 2) CA
  let CE := 3*K^2+1
  have hCP : 0 ≤ CP := firstModelDefectBudget_nonneg K (Cj 2) CA hK hCA
  have hCE : 0 ≤ CE := by dsimp only [CE];positivity
  refine ⟨η,CP*CE,hη,hη1,mul_nonneg hCP hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨A,hA⟩ := hAdjoint floor hf ε hε hSmall d hd CT P
  intro φ E D hφ b y hy
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hEnergy := D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy b
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  let Gr := fun p => (E.representative p).re
  let Gi := fun p => (E.representative p).im
  let hGr := Complex.reCLM.contDiff.comp E.representativeSmooth
  let hGi := Complex.imCLM.contDiff.comp E.representativeSmooth
  have hR := canonical_first_model_defect_form_bound hY d hg hK hd hf he hFrame P Gr hGr hy b
    (A b y) ((hA b).2 y hy).1 CA hCA hε ((hA b).2 y hy).2
  have hI := canonical_first_model_defect_form_bound hY d hg hK hd hf he hFrame P Gi hGi hy b
    (A b y) ((hA b).2 y hy).1 CA hCA hε ((hA b).2 y hy).2
  let xr := firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) Gr hGr b y
  let xi := firstModelDefectRealForm d (P.firstCovariantCoordinateCoarseL b) Gi hGi b y
  let Er := halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) Gr hGr) y
    (beta d.γ d.radius y) (axis b)
  let Ei := halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) Gi hGi) y
    (beta d.γ d.radius y) (axis b)
  have hr : |xr| ≤ CP*ε*Er := by
    exact hR
  have hi : |xi| ≤ CP*ε*Ei := by
    exact hI
  have he : metricDensity d.γ y*(Er+Ei) ≤ CE*physicalEnergyDensity d.γ d.frame d.radius φ y := hEnergy
  have hh := two_weighted_scalar_forms_bound (metricDensity d.γ y) CP CE ε xr xi Er Ei
    (physicalEnergyDensity d.γ d.frame d.radius φ y) hμ hCP hε hr hi he
  simpa only [PhysicalPrincipalData.firstModelDefectDensity,HarmonicTestExpansion.realSobolevSection,
    HarmonicTestExpansion.imagSobolevSection,xr,xi,Gr,Gi,hGr,hGi] using hh

end ShrinkingSpheres
