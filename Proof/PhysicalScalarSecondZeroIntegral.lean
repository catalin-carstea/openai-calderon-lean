import Proof.PhysicalScalarSecondZeroPoint
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

def scalarSecondZeroDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (q : X → ℝ) (a b : I) (y : X) : ℝ :=
  scalarCovariantSecondZeroDensity d q (E.realSobolevSection 2 (by norm_num)) (axis a) (axis b) y+
    scalarCovariantSecondZeroDensity d q (E.imagSobolevSection 2 (by norm_num)) (axis a) (axis b) y

/-- The actual scalar second-base/zero-adjoint cross term has a genuine
one-Green reduction and a common epsilon-squared original energy bound. -/
theorem uniform_physical_scalar_second_zero_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ i j a b : I,
      let q := scalarAdjointZeroProductWeight d.γ d.g₂ d.radius i j
      IntegrableOn (scalarSecondZeroDensity d E q a b) Y ∧
        IntegrableOn (scalarSecondZeroRemainderDensity d E q a b) Y ∧
        (∫ y in Y,scalarSecondZeroDensity d E q a b y)=
          (∫ y in Y,scalarSecondZeroRemainderDensity d E q a b y) ∧
        |∫ y in Y,scalarSecondZeroDensity d E q a b y| ≤
          C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C,hC,hPoint⟩ := uniform_physical_scalar_second_zero_remainder_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ i j a b
  let q := scalarAdjointZeroProductWeight d.γ d.g₂ d.radius i j
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  let Tr := scalarCovariantSecondZeroDensity d q Ur (axis a) (axis b)
  let Ti := scalarCovariantSecondZeroDensity d q Ui (axis a) (axis b)
  let Rr := scalarCovariantSecondZeroRemainder d q Ur (axis a) (axis b)
  let Ri := scalarCovariantSecondZeroRemainder d q Ui (axis a) (axis b)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hqS : ContDiffOn ℝ ∞ q Y := scalarAdjointZeroProductWeight_smooth hY hg hg2 hKpos
    d.radius hd.2.2.2.2.1.1 i j
  have hq (x : X) (hx : x ∈ E.supportSet) : ContDiffAt ℝ ∞ q x := hqS.contDiffAt (hY.mem_nhds (E.supportSubset hx))
  have h0R (x : X) (hx : x ∉ E.supportSet) : Ur x=0 := E.realSobolevSection_zero 2 (by norm_num) hx
  have h0I (x : X) (hx : x ∉ E.supportSet) : Ui x=0 := E.imagSobolevSection_zero 2 (by norm_num) hx
  have hRData := scalar_covariant_second_zero_reduction hY d hg hKpos he q Ur
    (E.contDiff_realSobolevSection 2 (by norm_num)) E.supportSet E.compactSupportSet E.supportSubset hq h0R (axis a) (axis b)
  have hIData := scalar_covariant_second_zero_reduction hY d hg hKpos he q Ui
    (E.contDiff_imagSobolevSection 2 (by norm_num)) E.supportSet E.compactSupportSet E.supportSubset hq h0I (axis a) (axis b)
  have hTr : Integrable Tr := hRData.1
  have hTi : Integrable Ti := hIData.1
  have hRr : Integrable Rr := hRData.2.1
  have hRi : Integrable Ri := hIData.2.1
  have hTInt : Integrable (scalarSecondZeroDensity d E q a b) := hTr.add hTi
  have hRInt : Integrable (scalarSecondZeroRemainderDensity d E q a b) := hRr.add hRi
  have hTOff (x : X) (hx : x ∉ Y) : scalarSecondZeroDensity d E q a b x=0 := by
    have hxS : x ∉ E.supportSet := fun hs => hx (E.supportSubset hs)
    have hr : Tr x=0 := scalarCovariantSecondZeroDensity_zero_off d q Ur (axis a) (axis b) x (h0R x hxS)
    have hi : Ti x=0 := scalarCovariantSecondZeroDensity_zero_off d q Ui (axis a) (axis b) x (h0I x hxS)
    change Tr x+Ti x=0
    rw [hr,hi,zero_add]
  have hROff (x : X) (hx : x ∉ Y) : scalarSecondZeroRemainderDensity d E q a b x=0 := by
    have hxS : x ∉ E.supportSet := fun hs => hx (E.supportSubset hs)
    have hr : Rr x=0 := scalarCovariantSecondZeroRemainder_zero_off d q Ur E.supportSet E.compactSupportSet.isClosed h0R (axis a) (axis b) x hxS
    have hi : Ri x=0 := scalarCovariantSecondZeroRemainder_zero_off d q Ui E.supportSet E.compactSupportSet.isClosed h0I (axis a) (axis b) x hxS
    change Rr x+Ri x=0
    rw [hr,hi,zero_add]
  have hTY : (∫ y in Y,scalarSecondZeroDensity d E q a b y)=(∫ y,scalarSecondZeroDensity d E q a b y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hTOff
  have hRY : (∫ y in Y,scalarSecondZeroRemainderDensity d E q a b y)=(∫ y,scalarSecondZeroRemainderDensity d E q a b y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hROff
  have hGlobal : (∫ x,scalarSecondZeroDensity d E q a b x)=(∫ x,scalarSecondZeroRemainderDensity d E q a b x) := by
    change (∫ x,Tr x+Ti x)=∫ x,Rr x+Ri x
    calc
      _ = (∫ x,Tr x)+(∫ x,Ti x) := integral_add hTr hTi
      _ = (∫ x,Rr x)+(∫ x,Ri x) := congrArg₂ (fun u v : ℝ => u+v) hRData.2.2 hIData.2.2
      _ = _ := (integral_add hRr hRi).symm
  have hEqY : (∫ y in Y,scalarSecondZeroDensity d E q a b y)=(∫ y in Y,scalarSecondZeroRemainderDensity d E q a b y) := by
    rw [hTY,hRY]
    exact hGlobal
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖scalarSecondZeroRemainderDensity d E q a b y‖ ≤
      (C*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint floor hf ε hε hε1 d hd φ E D hφ i j a b y hy
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ).const_mul (C*ε^2)
  have hRBound : |∫ y in Y,scalarSecondZeroRemainderDensity d E q a b y| ≤ C*ε^2*energySq Y d.γ d.frame d.radius φ := by
    have ht := norm_integral_le_of_norm_le hDom hBound
    simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using ht
  refine ⟨hTInt.integrableOn,hRInt.integrableOn,hEqY,?_⟩
  rw [hEqY]
  exact hRBound

end ShrinkingSpheres
