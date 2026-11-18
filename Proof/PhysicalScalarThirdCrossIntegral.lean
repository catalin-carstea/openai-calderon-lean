import Proof.PhysicalScalarThirdCrossPoint
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

def scalarThirdCrossDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (q : X → ℝ) (a b c : I) (y : X) : ℝ :=
  scalarCovariantThirdCrossDensity d q (E.realSobolevSection 2 (by norm_num)) (axis a) (axis b) (axis c) y+
    scalarCovariantThirdCrossDensity d q (E.imagSobolevSection 2 (by norm_num)) (axis a) (axis b) (axis c) y

lemma scalarCovariantThirdCrossDensity_zero_off (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (a b c x : X) (hx : x ∉ S) :
    scalarCovariantThirdCrossDensity d q U a b c x=0 := by
  simp only [scalarCovariantThirdCrossDensity,
    highSectionCovariantDerivative_zero_off d U S hS h0 c x hx,map_zero,inner_zero_right,mul_zero]

lemma scalarCovariantThirdCrossRemainder_zero_off (d : Data) (q : X → ℝ) (U : X → SphereSobolev 2)
    (S : Set X) (hS : IsClosed S) (h0 : ∀ x ∉ S,U x=0) (a b c x : X) (hx : x ∉ S) :
    scalarCovariantThirdCrossRemainder d q U a b c x=0 := by
  have hD (v : X) := highSectionCovariantDerivative_zero_off d U S hS h0 v x hx
  simp only [scalarCovariantThirdCrossRemainder,hD,map_zero,inner_zero_left,inner_zero_right,
    mul_zero,add_zero,sub_zero,zero_sub,neg_zero]

/-- A complete actual scalar-principal/adjoint third-base contribution:
genuine Green reduction and an epsilon-squared original global energy
bound, uniformly for all admitted configurations and canonical tests. -/
theorem uniform_physical_scalar_third_cross_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → ∀ i j l a b c : I,
      let q := scalarAdjointProductWeight d.γ d.g₂ d.radius i j l
      IntegrableOn (scalarThirdCrossDensity d E q a b c) Y ∧
        IntegrableOn (scalarThirdCrossRemainderDensity d E q a b c) Y ∧
        2*(∫ y in Y,scalarThirdCrossDensity d E q a b c y)=
          (∫ y in Y,scalarThirdCrossRemainderDensity d E q a b c y) ∧
        |2*(∫ y in Y,scalarThirdCrossDensity d E q a b c y)| ≤
          C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C,hC,hPoint⟩ := uniform_physical_scalar_third_cross_remainder_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ i j l a b c
  let q := scalarAdjointProductWeight d.γ d.g₂ d.radius i j l
  let Ur := E.realSobolevSection 2 (by norm_num)
  let Ui := E.imagSobolevSection 2 (by norm_num)
  let Tr := scalarCovariantThirdCrossDensity d q Ur (axis a) (axis b) (axis c)
  let Ti := scalarCovariantThirdCrossDensity d q Ui (axis a) (axis b) (axis c)
  let Rr := scalarCovariantThirdCrossRemainder d q Ur (axis a) (axis b) (axis c)
  let Ri := scalarCovariantThirdCrossRemainder d q Ui (axis a) (axis b) (axis c)
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hqS : ContDiffOn ℝ ∞ q Y := scalarAdjointProductWeight_smooth hY hg hg2 hKpos
    d.radius hd.2.2.2.2.1.1 i j l
  have hq (x : X) (hx : x ∈ E.supportSet) : ContDiffAt ℝ ∞ q x :=
    hqS.contDiffAt (hY.mem_nhds (E.supportSubset hx))
  have h0R (x : X) (hx : x ∉ E.supportSet) : Ur x=0 := E.realSobolevSection_zero 2 (by norm_num) hx
  have h0I (x : X) (hx : x ∉ E.supportSet) : Ui x=0 := E.imagSobolevSection_zero 2 (by norm_num) hx
  have hRData := scalar_covariant_third_cross_reduction hY d hg hKpos he hFrame q Ur
    (E.contDiff_realSobolevSection 2 (by norm_num)) E.supportSet E.compactSupportSet E.supportSubset hq h0R (axis a) (axis b) (axis c)
  have hIData := scalar_covariant_third_cross_reduction hY d hg hKpos he hFrame q Ui
    (E.contDiff_imagSobolevSection 2 (by norm_num)) E.supportSet E.compactSupportSet E.supportSubset hq h0I (axis a) (axis b) (axis c)
  have hTr : Integrable Tr := hRData.1
  have hTi : Integrable Ti := hIData.1
  have hRr : Integrable Rr := hRData.2.1
  have hRi : Integrable Ri := hIData.2.1
  have hTInt : Integrable (scalarThirdCrossDensity d E q a b c) := hTr.add hTi
  have hRInt : Integrable (scalarThirdCrossRemainderDensity d E q a b c) := hRr.add hRi
  have hTOff (x : X) (hx : x ∉ Y) : scalarThirdCrossDensity d E q a b c x=0 := by
    have hxS : x ∉ E.supportSet := fun hs => hx (E.supportSubset hs)
    change Tr x+Ti x=0
    have hr : Tr x=0 := scalarCovariantThirdCrossDensity_zero_off d q Ur E.supportSet E.compactSupportSet.isClosed h0R (axis a) (axis b) (axis c) x hxS
    have hi : Ti x=0 := scalarCovariantThirdCrossDensity_zero_off d q Ui E.supportSet E.compactSupportSet.isClosed h0I (axis a) (axis b) (axis c) x hxS
    rw [hr,hi,zero_add]
  have hROff (x : X) (hx : x ∉ Y) : scalarThirdCrossRemainderDensity d E q a b c x=0 := by
    have hxS : x ∉ E.supportSet := fun hs => hx (E.supportSubset hs)
    change Rr x+Ri x=0
    have hr : Rr x=0 := scalarCovariantThirdCrossRemainder_zero_off d q Ur E.supportSet E.compactSupportSet.isClosed h0R (axis a) (axis b) (axis c) x hxS
    have hi : Ri x=0 := scalarCovariantThirdCrossRemainder_zero_off d q Ui E.supportSet E.compactSupportSet.isClosed h0I (axis a) (axis b) (axis c) x hxS
    rw [hr,hi,zero_add]
  have hTY : (∫ y in Y,scalarThirdCrossDensity d E q a b c y)=
      (∫ y,scalarThirdCrossDensity d E q a b c y) := setIntegral_eq_integral_of_forall_compl_eq_zero hTOff
  have hRY : (∫ y in Y,scalarThirdCrossRemainderDensity d E q a b c y)=
      (∫ y,scalarThirdCrossRemainderDensity d E q a b c y) := setIntegral_eq_integral_of_forall_compl_eq_zero hROff
  have hGlobal : 2*(∫ x,scalarThirdCrossDensity d E q a b c x)=
      (∫ x,scalarThirdCrossRemainderDensity d E q a b c x) := by
    change 2*(∫ x,Tr x+Ti x)=∫ x,Rr x+Ri x
    calc
      _ = 2*((∫ x,Tr x)+(∫ x,Ti x)) := congrArg (fun r : ℝ => 2*r) (integral_add hTr hTi)
      _ = (∫ x,Rr x)+(∫ x,Ri x) := by linarith only [hRData.2.2,hIData.2.2]
      _ = _ := (integral_add hRr hRi).symm
  have hEqY : 2*(∫ y in Y,scalarThirdCrossDensity d E q a b c y)=
      (∫ y in Y,scalarThirdCrossRemainderDensity d E q a b c y) := by rw [hTY,hRY];exact hGlobal
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖scalarThirdCrossRemainderDensity d E q a b c y‖ ≤
      (C*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint floor hf ε hε hε1 d hd φ E D hφ i j l a b c y hy
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ).const_mul (C*ε^2)
  have hRBound : |∫ y in Y,scalarThirdCrossRemainderDensity d E q a b c y| ≤ C*ε^2*energySq Y d.γ d.frame d.radius φ := by
    have ht := norm_integral_le_of_norm_le hDom hBound
    simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using ht
  refine ⟨hTInt.integrableOn,hRInt.integrableOn,hEqY,?_⟩
  rw [hEqY]
  exact hRBound

end ShrinkingSpheres
