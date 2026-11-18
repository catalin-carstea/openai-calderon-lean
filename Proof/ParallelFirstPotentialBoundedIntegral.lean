import Proof.ParallelFirstPotentialComplex
import Proof.ParallelFirstPotentialBoundedPoint
import Proof.ParallelFirstPotentialBoundedIntegrability
import Proof.ParallelFirstSelfDefectSquareIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform bound for BOTH bounded correction/scalar-drift orientations
of the literal complete first/potential sector. -/
theorem uniform_first_potential_bounded_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (CF CG CK : ℝ) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) :
    ∃ CC : ℝ,0 ≤ CC ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      IntegrableOn (firstPotentialBoundedComplexDensity P W E) Y ∧
        |∫ y in Y,firstPotentialBoundedComplexDensity P W E y| ≤ CC*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨RF,hRF,hForward⟩ := uniform_effective_first_bounded_remainder hY hΩ (by omega) K ρ c₀ M Cj hK (1/2:ℝ)
  obtain ⟨RA,hRA,hAdjoint⟩ := uniform_effective_first_bounded_adjoint_half hY hΩ (by omega) K ρ c₀ M Cj hK
  let CQF := (physicalPotentialGeneratorBudget CF)^2*(49*potentialWordEntryBudget K)
  let CQA := (max (physicalPotentialGeneratorBudget CF) CG)^2*(49*potentialWordEntryBudget K)
  let CN := RF*CQF+RA*CQA
  let CC := 6*CN*(3*K^2+1)
  have hCQF : 0 ≤ CQF := by dsimp only [CQF,potentialWordEntryBudget];positivity
  have hCQA : 0 ≤ CQA := by dsimp only [CQA,potentialWordEntryBudget];positivity
  have hCN : 0 ≤ CN := by dsimp only [CN];positivity
  refine ⟨CC,by dsimp only [CC];positivity,?_⟩
  intro floor hf ε hε hε1 d hd CT P W φ E D hφ
  have hF := hForward floor hf ε hε hε1 d hd
  have hA := hAdjoint floor hf ε hε hε1 d hd
  have hIntR := firstPotentialBoundedDensity_integrable hY hΩ hSub hd (zero_lt_one.trans_le hK) P W hCG hCK
    (fun b => (hF b).1) (fun b => (hA b).1) (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hIntI := firstPotentialBoundedDensity_integrable hY hΩ hSub hd (zero_lt_one.trans_le hK) P W hCG hCK
    (fun b => (hF b).1) (fun b => (hA b).1) (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖firstPotentialBoundedComplexDensity P W E y‖ ≤
      (CC*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    let β := beta d.γ d.radius y
    have hβ1 : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hβ2 : 1 ≤ β^2 := by nlinarith only [hβ1]
    have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
    have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) :
        |firstPotentialBoundedDensity P W U y| ≤ (2*CN*ε^2)*(metricDensity d.γ y*∑ b : I,
          halfCovariantDirectionEnergy d (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b)) := by
      have hUD := (hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
      have hRow (b : I) :
          |⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
            (firstPotentialBoundedForwardHigherL d b y (firstSelfSourceDerivative d U y (axis b))),P.potentialQuadraticCoreSection W U y⟫_ℝ+
           ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
            (effectiveFirstBoundedAdjointHigherL d b y (firstSelfSourceDerivative d U y (axis b))),P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ| ≤
          CN*ε^2*halfCovariantDirectionEnergy d
            (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b) := by
        have hh := firstPotential_bounded_row_point_bound P hd hK hf hε hε1 hy hCG (W y hy) b hRF hRA
          (((hF b).2 y hy).trans (div_le_self (mul_nonneg hRF hε) hβ2))
          (((hA b).2 y hy).trans (div_le_self (mul_nonneg hRA hε) hβ2)) (U y) (firstSelfSourceDerivative d U y (axis b))
        simpa only [PhysicalPrincipalData.potentialQuadraticCoreSection,PhysicalPrincipalData.potentialQuadraticAdjointCoreSection,
          dite_eq_left hy,firstSelfSourceDerivative_inclusion d U hUD,halfCovariantDirectionEnergy,CN,CQF,CQA,β] using hh
      unfold firstPotentialBoundedDensity
      rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
      exact ((mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (by norm_num) hμ)).trans
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hRow b)) (mul_nonneg (by norm_num) hμ))).trans_eq
        (by rw [←Finset.mul_sum];ring)
    have hR := hPoint (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _).contDiffOn
    have hI := hPoint (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _).contDiffOn
    have hr : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (E.realHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.realSobolevSection (3/2:ℝ) (by norm_num) :=
      funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
    have hi : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
        (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num) x))=E.imagSobolevSection (3/2:ℝ) (by norm_num) :=
      funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
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
    unfold firstPotentialBoundedComplexDensity
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hR hI
      _ = (2*CN*ε^2)*(metricDensity d.γ y*((∑ b : I,halfCovariantDirectionEnergy d
          (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))+
          ∑ b : I,halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))) := by ring
      _ ≤ (2*CN*ε^2)*((3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hEnergy (by positivity)
      _ = _ := by dsimp only [CC];ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CC*ε^2)
  refine ⟨hIntR.add hIntI,?_⟩
  have hN := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN

end ShrinkingSpheres.ParallelEnergy
