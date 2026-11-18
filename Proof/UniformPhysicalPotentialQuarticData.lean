import Proof.PhysicalPotentialGeneratorFrameChange
import Proof.UniformActualFirstAdjointEndpoints
import Proof.UniformNativeTaylorGeneratorBounds
import Proof.HalfTaylorAdjointDefect
import Proof.UniformNativeRelativeSymmetricHigherData
import Proof.ActualFirstErrorNativeIdentification
import Proof.RelativeCenterAngularCoefficient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Closed common uniform production of ALL actual potential mixed-adjoint
quartic data, for ANY already selected physical principal data. The constants
precede the radius profile, smooth frame, floor and smallness parameter. -/
theorem uniform_physical_potential_quartic_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CADJ CK : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CADJ ∧ 0 ≤ CK ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,
      Nonempty (PhysicalPotentialQuarticData P y CADJ CK) := by
  classical
  have hT := uniform_native_relative_horizontal_taylor_data (Y:=Y) (Ω:=Ω) (m:=m)
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηT,CFT,CAT,CMT,CQ,CI,CW,F0,hηT,hηT1,hCFT,hCAT,hCMT,hCQ,hCI,hCW,hF0,hNative⟩ := hT
  have hC := uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ := hC
  have hV := uniform_native_relative_symmetric_higher_data hY hΩ 0 (by omega)
    K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨ηV,CFV,CAV,hηV,hηV1,hCFV,hCAV,hSym⟩ := hV
  have hE := uniform_actual_first_adjoint_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hEndpoints⟩ := hE
  obtain ⟨Q0,hQ0⟩ := exists_unit_boundary_coefficient
  have hG := uniform_native_taylor_generator_bounds hY hΩ hSub hm K ρ c₀ M Cj hK hρ
    CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0
  obtain ⟨ηG,CG,hηG,hηG1,hCG,hGenerator⟩ := hG
  have hD := uniform_native_adjoint_half_taylor_defect hY hΩ hm K ρ c₀ M Cj hK hρ
    CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0
  obtain ⟨ηD,CKN,hηD,hηD1,hCKN,hDefect⟩ := hD
  have ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous _ _ _
      (continuous_pi (fun i => continuous_pi (fun j => (contDiff_coefficientValue 2 (F0 i j)).continuous)))
      continuous_const continuous_const
  obtain ⟨CAng,hCAng,hAngular⟩ := RelativeCenterErrorCoefficientFamily.uniform_angularCoefficient_two_jets
    (Ω:=Ω) hΩ (show 2 ≤ m by omega) K M hK
  let CR := (CAng+2)*CC
  let QB := nativePotentialScalarBudget Q0 K (M 0) CC
  let ZB := firstErrorScalarPacketBoundedBudget Q0 CQ K (M 0) CC
  let AB := nativePotentialAngularBudget Q0 K (M 0) CC CR
  have hJ : 0 ≤ firstErrorScalarFixedBudget Q0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hQB : 0 ≤ QB := (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hJ).trans (le_max_left _ _)
  have hAB : 0 ≤ AB := (mul_nonneg (by norm_num : (0:ℝ) ≤ 76) hJ).trans (le_max_left _ _)
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hM := uniform_native_scalar_mixed_adjoint_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
    CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0 ha0 CG QB ZB AB hQB hAB
  obtain ⟨ηM,CS,hηM,hηM1,hCS,hMixed⟩ := hM
  let CA := nativeScalarBoundedAdjointHigherBudget F0 ha0 CG CKN QB ZB
  have hCA : 0 ≤ CA := abs_nonneg _
  let η := min ηT (min ηC (min ηV (min ηE (min ηG (min ηM ηD)))))
  have hη : 0 < η := lt_min hηT (lt_min hηC (lt_min hηV (lt_min hηE (lt_min hηG (lt_min hηM hηD)))))
  refine ⟨η,3*K*CA,9*K^2*CS,hη,(min_le_left _ _).trans hηT1,by positivity,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P y hy
  have hSmallValues : ε ≤ ηT ∧ ε ≤ ηC ∧ ε ≤ ηV ∧ ε ≤ ηE ∧ ε ≤ ηG ∧ ε ≤ ηM ∧ ε ≤ ηD := by
    simpa only [η,le_min_iff] using hSmall
  obtain ⟨hSmallT,hSmallC,hSmallV,hSmallE,hSmallG,hSmallM,hSmallD⟩ := hSmallValues
  have hε1 := hSmallT.trans hηT1
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 := hrε.trans hε1
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
  obtain ⟨G⟩ := hGenerator floor hf ε hε hSmallG d hd y hy CFT CAT CMT s
  obtain ⟨V⟩ := hSym floor hf ε hε hSmallV d hd y hy CQ CFT CAT CMT s
  let Ca : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH :=
    fun a j => Classical.choice (hCoeff floor hf ε hε hSmallC d hd y hy (axis a) j)
  choose Lo Hi hLS hHS hAll using fun a : I => hEndpoints floor hf ε hε hSmallE d hd (axis a)
    P.radial P.adjoint (P.center a) P.radial_actual P.adjoint_pair (P.center_actual a)
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hEq (a : I) := (s.actual_first_error_native_identification V.neighborhood hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hy hr.ne' hd.2.2.2.2.1.1 (Ca a) P.radial P.adjoint (P.center a)
    P.radial_actual P.adjoint_pair (P.center_actual a) hF0 (Lo a y) (hAll a y hy).1).1
  have hLN (a : I) : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (s.firstAdjointErrorFamily (Ca a) p)=
      (Lo a y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    rw [←hEq a]
    exact (hAll a y hy).1
  have hHN (a : I) : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi a y)=
      (s.firstAdjointErrorFamily (Ca a) p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    rw [←hEq a]
    exact (hAll a y hy).2.1
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have hAng (a i j k : I) : ‖RelativeCenterErrorCoefficientFamily.angularCoefficient (Ca a) k i j p‖ ≤
      CR*‖axis a‖*(d.radius y)^2 := by
    have hh := (hAngular d hd.1 y (hSub hy) (axis a) CC CH (zero_le_one.trans hCC) (Ca a) he k i j).bound 0 (by norm_num)
    simpa only [norm_iteratedFDeriv_zero,CR,mul_assoc] using hh
  have hEP (a : I) : Nonempty (NativeFirstErrorScalarHigherPacket G (Lo a y) (Hi a y) Q0 (M 0) CC CR (d.radius y)) := by
    simpa only [norm_axis,one_mul] using G.first_error_scalar_higher_packet hd hK hf hε hε1 hy hr1
      (zero_le_one.trans hCQ) hF0 Q0 hQ0 (zero_le_one.trans hCC) (axis a) (Ca a) CR hCR (hAng a)
      (Lo a y) (Hi a y) (hLN a) (hHN a)
  obtain ⟨Packets⟩ := native_potential_scalar_packet_family G hF0 Q0 hQ0 (M 0) CC CR hr.le
    (fun a => Lo a y) (fun a => Hi a y) (fun a => Classical.choice (hEP a))
  have hMixedPoint := hMixed floor hf ε hε hSmallM d hd y hy CFT CAT CMT s G
  obtain ⟨KN,hKNJets,hP⟩ := hDefect floor hf ε hε hSmallD d hd y hy CFT CAT CMT s
  have hKN : ‖KN p‖ ≤ CKN*(d.radius y)^2 := by
    simpa only [norm_iteratedFDeriv_zero] using hKNJets.bound 0 (by norm_num)
  obtain ⟨W⟩ := Packets.quartic_data hMixedPoint hF0 ha0 (zero_le_one.trans hCQ) hCI hCW hr.le hr1
    (KN p) CKN hCKN hKN hP
  exact P.quartic_data_of_axis_generators hd hK hy (fun a => Lo a y) (fun a => Hi a y)
    (fun a => (hAll a y hy).1) (fun a => (hAll a y hy).2.1) hCS W
end ShrinkingSpheres
