import Proof.ParallelFirstSelfLeadingComplexPoint
import Proof.ParallelFirstSelfLeadingBudgets
import Proof.BackgroundScalarCurvatureTripleBound
import Proof.EnergyPositivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Complete uniform leading-square comparison. Its Hodge argument uses
the SAME fixed P/WF/W; constants precede every profile, frame and test. -/
theorem uniform_first_self_leading_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT CB CS CG CK : ℝ)
    (hCB : 0 ≤ CB) (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        IntegrableOn (firstSelfLeadingComplexDensity P WF E) Y ∧
        |∫ y in Y,firstSelfLeadingComplexDensity P WF E y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨L⟩ := first_self_leading_low_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨J⟩ := first_self_leading_high_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨S⟩ := first_self_leading_scalar_budget hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨F⟩ := first_self_leading_forward_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CL := L.boundConstant
  let CJ := J.boundConstant
  let CA := 3*K*CB+S.boundConstant
  let MQ := 27*K*|M ⟨1,by omega⟩|
  let CR := fixedDirectionAngularCurvatureBudget (by omega : 2 ≤ m) K M
  let HR := 27*(CA^2*CR+2*MQ*CA*(CL+CJ))*(3*K^2+1)
  let HP := 162*CJ*(CL+CJ)*(3*K^2+1)
  have hCL : 0 ≤ CL := L.nonneg
  have hCJ : 0 ≤ CJ := J.nonneg
  have hSC : 0 ≤ S.boundConstant := S.nonneg
  have hCA : 0 ≤ CA := by dsimp only [CA];positivity
  have hMQ : 0 ≤ MQ := by dsimp only [MQ];positivity
  have hCR : 0 ≤ CR := fixedDirectionAngularCurvatureBudget_nonneg _ K (zero_le_one.trans hK) M
  have hHR : 0 ≤ HR := by dsimp only [HR];positivity
  have hHP : 0 ≤ HP := by dsimp only [HP];positivity
  refine ⟨min L.eta (min J.eta F.eta),9*CS+HR+HP,
    lt_min L.eta_pos (lt_min J.eta_pos F.eta_pos),(min_le_left _ _).trans L.eta_le_one,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ E D hφ
  have hSmallL := hSmall.trans (min_le_left _ _)
  have hSmallJ := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallF := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 := hSmallL.trans L.eta_le_one
  have hKpos := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hw (b : I) := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hKpos b
  have hJets := J.packet floor hf ε hε hSmallJ d hd CF CT P CB CS WF
  have hRaw := F.raw floor hf ε hε hSmallF d hd CF CT P
  have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) {y : X} (hy : y ∈ Y) :
      FirstSelfAdjointSourcePointBounds P WF W U y CA CL CJ := by
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hLow (b : I) : ‖P.firstCovariantCoordinateHalfL b y‖ ≤ CL*ε :=
      (L.bound floor hf ε hε hSmallL d hd CF CT P b y hy).trans (div_le_self (mul_nonneg hCL hε) hβ)
    have hA (b : I) : ‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε := by
      have hCoord := (WF.norm_coordinateAdjointHigher_le hd hK b hy).trans
        (div_le_self (by positivity : 0 ≤ (3*K*CB)*ε) hβ)
      have hScalar := (norm_scalar_higher_inclusion_le (scalarPrincipalConnectionWeight d b y)).trans
        (S.bound floor hf ε hε hε1 d hd b y hy)
      exact ((norm_sub_le _ _).trans (add_le_add hCoord hScalar)).trans_eq (by dsimp only [CA];ring)
    exact first_self_adjoint_source_point_bounds hY hΩ hd hKpos P WF W U hU hw hy hCJ hε hA hLow hJets
  have hEnergyI := hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKpos d.frame he hFrame hf hφ
  have hHodge := first_self_actual_adjoint_hodge_complex_integral hY hSub hd hKpos P WF W E
  have hLeadingI := (firstSelf_complex_core_split_integrableOn hY hΩ hSub hd hKpos P WF W hCG hCK E).1
  obtain ⟨hAngularI,hAngularN⟩ := firstSelfAngularComplexDensity_integral_bound hY hΩ hd hK hf hε hε1 P WF hCS E D hφ
  have hPerturbI : IntegrableOn (firstSelfLeadingPerturbationComplexDensity P WF W E) Y :=
    (hLeadingI.sub hAngularI).sub hHodge.1
  have hBounds : ∀ᵐ y ∂volume.restrict Y,
      ‖firstSelfAdjointSourceHodgeComplexRemainder WF E y‖ ≤ (HR*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y ∧
      ‖firstSelfLeadingPerturbationComplexDensity P WF W E y‖ ≤ (HP*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hPR := hPoint (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_realHigherSobolevSection _ _).contDiffOn hy
    have hPI := hPoint (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_imagHigherSobolevSection _ _).contDiffOn hy
    have hDμ (i : I) : |fderiv ℝ (metricDensity d.γ) y (axis i)| ≤ MQ*metricDensity d.γ y :=
      hd.relative_density_axis_bound hΩ (by omega) hKpos hy i
    have hCurv (b c : I) : ‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c)‖ ≤ CR := by
      simpa only [norm_axis,mul_one,CR,fixedDirectionAngularCurvatureBudget] using
        Background.norm_frameCurvatureSobolevL_le (1/2:ℝ) hΩ hK (by omega) hd.1 (hSub hy) (axis b) (axis c)
    constructor
    · rw [Real.norm_eq_abs]
      exact first_self_hodge_complex_remainder_point_bound hY hg hK he hFrame P WF W E D hφ hy
        hPR hPI hCA hCL hCJ hMQ hCR hε hβ hDμ hCurv
    · rw [Real.norm_eq_abs]
      exact first_self_leading_complex_perturbation_point_bound hY hg hK he hFrame hd P WF W E D hφ hy
        hPR hPI hCL hCJ hε hβ (hRaw y hy)
  have hRN : |∫ y in Y,firstSelfAdjointSourceHodgeComplexRemainder WF E y| ≤ HR*ε^2*energySq Y d.γ d.frame d.radius φ := by
    have hN := norm_integral_le_of_norm_le (hEnergyI.const_mul (HR*ε^2)) (hBounds.mono (fun _ h => h.1))
    simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN
  have hPN : |∫ y in Y,firstSelfLeadingPerturbationComplexDensity P WF W E y| ≤ HP*ε^2*energySq Y d.γ d.frame d.radius φ := by
    have hN := norm_integral_le_of_norm_le (hEnergyI.const_mul (HP*ε^2)) (hBounds.mono (fun _ h => h.2))
    simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN
  have hHN : |∫ y in Y,firstSelfAdjointSourceHodgeComplexDensity P WF W E y| ≤ HR*ε^2*energySq Y d.γ d.frame d.radius φ := by
    rw [hHodge.2.2]
    exact hRN
  have hεsq : ε^2 ≤ ε := by nlinarith only [hε,hε1]
  have hEnergy := energySq_nonneg Y d.γ d.frame d.radius φ
  have hHN' := hHN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεsq hHR) hEnergy)
  have hPN' := hPN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεsq hHP) hEnergy)
  let A := firstSelfAngularComplexDensity WF E
  let H := firstSelfAdjointSourceHodgeComplexDensity P WF W E
  let R := firstSelfLeadingPerturbationComplexDensity P WF W E
  have hFun : firstSelfLeadingComplexDensity P WF E=(fun y => A y+H y+R y) :=
    funext (firstSelfLeadingComplexDensity_eq_hodge_split P WF W E)
  have hInt : (∫ y in Y,firstSelfLeadingComplexDensity P WF E y)=
      (∫ y in Y,A y)+(∫ y in Y,H y)+(∫ y in Y,R y) := by
    rw [hFun]
    change (∫ y in Y,(A+H+R) y)=_
    exact (integral_add (hAngularI.add hHodge.1) hPerturbI).trans
      (congrArg (fun t => t+∫ y in Y,R y) (integral_add hAngularI hHodge.1))
  refine ⟨hLeadingI,?_⟩
  rw [hInt]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hAngularN hHN') hPN').trans_eq (by ring))

end ShrinkingSpheres.ParallelEnergy
