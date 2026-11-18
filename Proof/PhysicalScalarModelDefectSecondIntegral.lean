import Proof.PhysicalScalarModelDefectSecondPoint
import Proof.AmbientHigherSobolevSection
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

def physicalScalarModelDefectSecondDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (q : X → ℝ) (a b : I) (y : X) : ℝ :=
  scalarModelDefectSecondDensity d q (E.realSobolevSection 2 (by norm_num))
    (ambientHigherSobolevSection 3 (by norm_num) (fun p => (E.representative p).re)
      (Complex.reCLM.contDiff.comp E.representativeSmooth)) (axis a) (axis b) y+
  scalarModelDefectSecondDensity d q (E.imagSobolevSection 2 (by norm_num))
    (ambientHigherSobolevSection 3 (by norm_num) (fun p => (E.representative p).im)
      (Complex.imCLM.contDiff.comp E.representativeSmooth)) (axis a) (axis b) y

/-- Complete actual scalar principal/model-adjoint-defect contribution.
The higher sections are constructed from the supplied smooth representative,
their genuine inclusion is proved, and one covariant Green reduction gives
integrability and a common original global energy bound. -/
theorem uniform_physical_scalar_model_defect_second_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ i j a b : I,
      let q := scalarPrincipalDensityWeight d.γ d.g₂ d.radius i j
      IntegrableOn (physicalScalarModelDefectSecondDensity d E q a b) Y ∧
        IntegrableOn (scalarModelDefectSecondRemainderDensity d E q a b) Y ∧
        (∫ y in Y,physicalScalarModelDefectSecondDensity d E q a b y)=
          (∫ y in Y,scalarModelDefectSecondRemainderDensity d E q a b y) ∧
        |∫ y in Y,physicalScalarModelDefectSecondDensity d E q a b y| ≤
          C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C,hC,hPoint⟩ := uniform_physical_scalar_model_defect_second_remainder_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ i j a b
  let q := scalarPrincipalDensityWeight d.γ d.g₂ d.radius i j
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  let Vr := ambientHigherSobolevSection 3 (by norm_num) (fun p => (E.representative p).re)
    (Complex.reCLM.contDiff.comp E.representativeSmooth)
  let Vi := ambientHigherSobolevSection 3 (by norm_num) (fun p => (E.representative p).im)
    (Complex.imCLM.contDiff.comp E.representativeSmooth)
  let Tr := scalarModelDefectSecondDensity d q Ur Vr (axis a) (axis b)
  let Ti := scalarModelDefectSecondDensity d q Ui Vi (axis a) (axis b)
  let Rr := scalarModelDefectSecondRemainder d q Ur (axis a) (axis b)
  let Ri := scalarModelDefectSecondRemainder d q Ui (axis a) (axis b)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun u v => (hd.1.1.1 u v).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun u v => (hd.1.2.2.1.1 u v).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (k : I) : ContDiffOn ℝ ∞ (fun x => d.frame x k) Y := (hd.1.2.2.2.2.2.2.1 k).mono hSub
  have hFrame : ∀ x ∈ Y,∀ u v,metricPair d.γ x (d.frame x u) (d.frame x v)=if u=v then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have ha : ContDiffOn ℝ ∞ (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x i j) Y :=
    hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hKpos i j)
  have hqS : ContDiffOn ℝ ∞ q Y := (hg.contDiffOn_density hKpos).mul ha
  have hq (x : X) (hx : x ∈ E.supportSet) : ContDiffAt ℝ ∞ q x := hqS.contDiffAt (hY.mem_nhds (E.supportSubset hx))
  have hCR (x : X) : sphereSobolevInclusionL 3 2 (by norm_num) (Vr x)=Ur x :=
    ambientHigherSobolevSection_inclusion 3 2 (by norm_num) (by norm_num) (by norm_num) _ _ x
  have hCI (x : X) : sphereSobolevInclusionL 3 2 (by norm_num) (Vi x)=Ui x :=
    ambientHigherSobolevSection_inclusion 3 2 (by norm_num) (by norm_num) (by norm_num) _ _ x
  have hVR : ContDiff ℝ ∞ Vr := contDiff_ambientHigherSobolevSection 3 (by norm_num) _ _
  have hVI : ContDiff ℝ ∞ Vi := contDiff_ambientHigherSobolevSection 3 (by norm_num) _ _
  have h0R (x : X) (hx : x ∉ E.supportSet) : Ur x=0 := E.realSobolevSection_zero 2 (by norm_num) hx
  have h0I (x : X) (hx : x ∉ E.supportSet) : Ui x=0 := E.imagSobolevSection_zero 2 (by norm_num) hx
  have h0VR (x : X) (hx : x ∉ E.supportSet) : Vr x=0 := by
    apply sphereSobolevInclusionL_injective 3 2 (by norm_num)
    rw [hCR x,h0R x hx,map_zero]
  have h0VI (x : X) (hx : x ∉ E.supportSet) : Vi x=0 := by
    apply sphereSobolevInclusionL_injective 3 2 (by norm_num)
    rw [hCI x,h0I x hx,map_zero]
  have hRData := scalar_model_defect_second_reduction hY d hg hKpos he hFrame hlog q Ur Vr hCR
    (E.contDiff_realSobolevSection 2 (by norm_num)) hVR E.supportSet E.compactSupportSet E.supportSubset hq h0R h0VR (axis a) (axis b)
  have hIData := scalar_model_defect_second_reduction hY d hg hKpos he hFrame hlog q Ui Vi hCI
    (E.contDiff_imagSobolevSection 2 (by norm_num)) hVI E.supportSet E.compactSupportSet E.supportSubset hq h0I h0VI (axis a) (axis b)
  have hTr : Integrable Tr := hRData.1
  have hTi : Integrable Ti := hIData.1
  have hRr : Integrable Rr := hRData.2.1
  have hRi : Integrable Ri := hIData.2.1
  have hTInt : Integrable (physicalScalarModelDefectSecondDensity d E q a b) := hTr.add hTi
  have hRInt : Integrable (scalarModelDefectSecondRemainderDensity d E q a b) := hRr.add hRi
  have hTOff (x : X) (hx : x ∉ Y) : physicalScalarModelDefectSecondDensity d E q a b x=0 := by
    have hxS : x ∉ E.supportSet := fun hs => hx (E.supportSubset hs)
    change Tr x+Ti x=0
    have hr : Tr x=0 := scalarModelDefectSecondDensity_zero_off d q Ur Vr (axis a) (axis b) x (h0R x hxS)
    have hi : Ti x=0 := scalarModelDefectSecondDensity_zero_off d q Ui Vi (axis a) (axis b) x (h0I x hxS)
    rw [hr,hi,zero_add]
  have hROff (x : X) (hx : x ∉ Y) : scalarModelDefectSecondRemainderDensity d E q a b x=0 := by
    have hxS : x ∉ E.supportSet := fun hs => hx (E.supportSubset hs)
    change Rr x+Ri x=0
    have hr : Rr x=0 := scalarModelDefectSecondRemainder_zero_off d q Ur E.supportSet E.compactSupportSet.isClosed h0R (axis a) (axis b) x hxS
    have hi : Ri x=0 := scalarModelDefectSecondRemainder_zero_off d q Ui E.supportSet E.compactSupportSet.isClosed h0I (axis a) (axis b) x hxS
    rw [hr,hi,zero_add]
  have hTY : (∫ y in Y,physicalScalarModelDefectSecondDensity d E q a b y)=(∫ y,physicalScalarModelDefectSecondDensity d E q a b y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hTOff
  have hRY : (∫ y in Y,scalarModelDefectSecondRemainderDensity d E q a b y)=(∫ y,scalarModelDefectSecondRemainderDensity d E q a b y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hROff
  have hGlobal : (∫ x,physicalScalarModelDefectSecondDensity d E q a b x)=(∫ x,scalarModelDefectSecondRemainderDensity d E q a b x) := by
    change (∫ x,Tr x+Ti x)=∫ x,Rr x+Ri x
    calc
      _ = (∫ x,Tr x)+(∫ x,Ti x) := integral_add hTr hTi
      _ = (∫ x,Rr x)+(∫ x,Ri x) := congrArg₂ (fun u v : ℝ => u+v) hRData.2.2 hIData.2.2
      _ = _ := (integral_add hRr hRi).symm
  have hEqY : (∫ y in Y,physicalScalarModelDefectSecondDensity d E q a b y)=(∫ y in Y,scalarModelDefectSecondRemainderDensity d E q a b y) := by
    rw [hTY,hRY];exact hGlobal
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖scalarModelDefectSecondRemainderDensity d E q a b y‖ ≤
      (C*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint floor hf ε hε hε1 d hd φ E D hφ i j a b y hy
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ).const_mul (C*ε)
  refine ⟨hTInt.integrableOn,hRInt.integrableOn,hEqY,?_⟩
  rw [hEqY]
  have ht := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using ht

end ShrinkingSpheres
