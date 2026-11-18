import Proof.ParallelFirstSelfDefectCrossPoint
import Proof.ParallelFirstSelfDefectSquareIntegral
import Proof.UniformEffectiveFirstLowEndpointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform bound for the EXACT leading/complete-defect cross premise
of the first-self core split, using the common fixed adjoint witnesses. -/
theorem uniform_first_self_defect_cross_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CB CG CK : ℝ)
    (hCB : 0 ≤ CB) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ η CC : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CC ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      IntegrableOn (firstSelfDefectCrossComplexDensity P WF W E) Y ∧
        |∫ y in Y,firstSelfDefectCrossComplexDensity P WF W E y| ≤
          CC*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨ηD,CR,hηD,hηD1,hCR,hDefect⟩ := uniform_first_adjoint_defect_higher_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hLow⟩ := uniform_effective_first_low_endpoint_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CC := 6*CR*CL*(3*K^2+1)
  refine ⟨min ηD ηL,CC,lt_min hηD hηL,(min_le_left _ _).trans hηD1,by dsimp only [CC];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS P WF W φ E D hφ
  have hSmallD := hSmall.trans (min_le_left _ _)
  have hSmallL := hSmall.trans (min_le_right _ _)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hInt := (firstSelf_complex_core_split_integrableOn hY hΩ hSub hd
    (zero_lt_one.trans_le hK) P WF W hCG hCK E).2.1
  have hr : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.realSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hi : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖firstSelfDefectCrossComplexDensity P WF W E y‖ ≤
      (CC*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    let β := beta d.γ d.radius y
    have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
    have hL (b : I) : ‖P.firstCovariantCoordinateHalfL b y‖ ≤ CL*ε :=
      ((hLow floor hf ε hε hSmallL d hd CF CT P b).2 y hy).trans
        (div_le_self (mul_nonneg hCL hε) hβ)
    have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) :
        |firstSelfDefectCrossDensity P WF W U y| ≤
          (2*CR*CL*ε^2)*(metricDensity d.γ y*∑ b : I,halfCovariantDirectionEnergy d
            (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b)) := by
      obtain ⟨R,hR,hRN⟩ := hDefect floor hf ε hε hSmallD d hd CF CT CS CG CK P WF W U hU y hy
      have hN := first_self_defect_cross_inner_le P WF W U hy
        ((hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
        hCL hCR hε (zero_lt_one.trans_le hβ) hL R hR hRN
      unfold firstSelfDefectCrossDensity
      rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
      exact (mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) hμ)).trans_eq (by ring)
    have hR := hPoint (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_realHigherSobolevSection _ _).contDiffOn
    have hI := hPoint (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
      (E.contDiff_imagHigherSobolevSection _ _).contDiffOn
    rw [hr] at hR
    rw [hi] at hI
    have hEnergy : metricDensity d.γ y*((∑ b : I,halfCovariantDirectionEnergy d
        (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))+
        ∑ b : I,halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b)) ≤
        (3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      calc
        _ = ∑ b : I,metricDensity d.γ y*(halfCovariantDirectionEnergy d
            (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b)+
            halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b)) := by
          rw [←Finset.sum_add_distrib,Finset.mul_sum]
        _ ≤ ∑ _b : I,(3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y :=
          Finset.sum_le_sum (fun b _ => D.half_covariant_direction_energy_le hY hg hK he hFrame hφ.1 hy b)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
    rw [Real.norm_eq_abs]
    unfold firstSelfDefectCrossComplexDensity
    calc
      _ ≤ |firstSelfDefectCrossDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y|+
          |firstSelfDefectCrossDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y| := abs_add_le _ _
      _ ≤ _ := add_le_add hR hI
      _ = (2*CR*CL*ε^2)*(metricDensity d.γ y*((∑ b : I,halfCovariantDirectionEnergy d
          (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))+
          ∑ b : I,halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))) := by ring
      _ ≤ (2*CR*CL*ε^2)*((3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hEnergy (by positivity)
      _ = _ := by dsimp only [CC];ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CC*ε^2)
  refine ⟨hInt,?_⟩
  have hN := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN

end ShrinkingSpheres.ParallelEnergy
