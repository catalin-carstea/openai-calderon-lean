import Proof.ParallelFirstSelfLeadingExchange
import Proof.ParallelFirstSelfIntegrability
import Proof.PhysicalFirstCoordinateCommutatorIntegral

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

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstSelfAngularComplexDensity {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfAngularDensity WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfAngularDensity WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstSelfExchangeDefectComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfExchangeDefectDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfExchangeDefectDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

lemma firstSelfAngularComplexDensity_eq_coordinate {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    firstSelfAngularComplexDensity WF E=D.coordinateFirstCommutatorDensity WF.coordinateCommLow := by
  have hr : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hi : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  funext y
  unfold firstSelfAngularComplexDensity firstSelfAngularDensity
  rw [hr,hi]
  simp only [AngularModelData.coordinateFirstCommutatorDensity,
    AngularComponentData.coordinateFirstCommutatorForm,HarmonicTestExpansion.realSobolevSection,
    HarmonicTestExpansion.imagSobolevSection,Complex.reCLM_apply,Complex.imCLM_apply]
  ring

/-- The angular part of the SAME physical leading-square cancellation is
already uniformly bounded, for ANY fixed coherent WF. -/
theorem firstSelfAngularComplexDensity_integral_bound
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (hCS : 0 ≤ CS)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) :
    IntegrableOn (firstSelfAngularComplexDensity WF E) Y ∧
      |∫ y in Y,firstSelfAngularComplexDensity WF E y| ≤
        (9*CS)*ε*energySq Y d.γ d.frame d.radius φ := by
  rw [firstSelfAngularComplexDensity_eq_coordinate WF E D]
  exact WF.integral_coordinate_density_bound hY hΩ hd hK hf hε hε1 hCS E D hφ

lemma firstSelfComplexDensity_eq_angular_exchange_defect
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    firstSelfComplexDensity P WF W E y=
      firstSelfAngularComplexDensity WF E y+firstSelfExchangeDefectComplexDensity P WF W E y := by
  have hr := firstSelfDensity_eq_angular_exchange_defect hY hd P WF W
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) hy
    ((E.contDiff_realHigherSobolevSection _ _).differentiable (by simp) y) hRaw
  have hi := firstSelfDensity_eq_angular_exchange_defect hY hd P WF W
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) hy
    ((E.contDiff_imagHigherSobolevSection _ _).differentiable (by simp) y) hRaw
  unfold firstSelfComplexDensity firstSelfAngularComplexDensity firstSelfExchangeDefectComplexDensity
  rw [hr,hi]
  ring

/-- A narrower checked caller leaves only the GROUPED covariant exchange
and full adjoint defect integral to estimate. All its domains are produced. -/
theorem firstSelfComplexDensity_integral_bound_of_exchange_defect
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ)
    (hRaw : ∀ y ∈ Y,∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (CR : ℝ) (hRest : |∫ y in Y,firstSelfExchangeDefectComplexDensity P WF W E y| ≤
      CR*ε*energySq Y d.γ d.frame d.radius φ) :
    IntegrableOn (firstSelfExchangeDefectComplexDensity P WF W E) Y ∧
    IntegrableOn (firstSelfComplexDensity P WF W E) Y ∧
      |∫ y in Y,firstSelfComplexDensity P WF W E y| ≤
        (9*CS+CR)*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨hAngular,hAngularN⟩ := firstSelfAngularComplexDensity_integral_bound
    hY hΩ hd hK hf hε hε1 P WF hCS E D hφ
  have hFull := firstSelfComplexDensity_integrableOn hY hΩ hSub hd
    (zero_lt_one.trans_le hK) P WF W hCG hCK E
  have hEq : firstSelfComplexDensity P WF W E =ᵐ[volume.restrict Y]
      fun y => firstSelfAngularComplexDensity WF E y+firstSelfExchangeDefectComplexDensity P WF W E y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact firstSelfComplexDensity_eq_angular_exchange_defect hY hd P WF W E hy (hRaw y hy)
  have hRestEq : (fun y => firstSelfComplexDensity P WF W E y-firstSelfAngularComplexDensity WF E y)
      =ᵐ[volume.restrict Y] firstSelfExchangeDefectComplexDensity P WF W E := by
    filter_upwards [hEq] with y hy
    rw [hy]
    ring
  have hRestInt := (hFull.sub hAngular).congr hRestEq
  refine ⟨hRestInt,hFull,?_⟩
  rw [integral_congr_ae hEq,integral_add hAngular hRestInt]
  exact ((abs_add_le _ _).trans (add_le_add hAngularN hRest)).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
