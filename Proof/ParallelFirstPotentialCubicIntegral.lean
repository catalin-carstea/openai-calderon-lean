import Proof.ParallelFirstPotentialComplex
import Proof.ParallelFirstPotentialCubicPoint
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

/-- Quantitative complete angular-cubic integral. Its qualitative
integrability is supplied by the already integrable exact density split,
so no measurable dependence of the chosen W commutator lifts is assumed. -/
theorem firstPotential_cubic_complex_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (CF CG CK : ℝ) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (floor ε : ℝ) (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (d : Data)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (CT : ℝ)
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (φ : Field) (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : Test Y d.γ d.frame φ) (hInt : IntegrableOn (firstPotentialCubicComplexDensity P W E) Y) :
    let BW := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)+6+
      3*principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
    let G := max (physicalPotentialGeneratorBudget CF) CG
    let CQ := 49*potentialWordEntryBudget K
    |∫ y in Y,firstPotentialCubicComplexDensity P W E y| ≤
      (6*BW*(6*K*G*CK*CQ)*(3*K^2+1))*ε^2*energySq Y d.γ d.frame d.radius φ := by
  let BW := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)+6+
    3*principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CQ := 49*potentialWordEntryBudget K
  let CN := 6*K*G*CK*CQ
  let CC := 6*BW*CN*(3*K^2+1)
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hCQ : 0 ≤ CQ := by dsimp only [CQ,potentialWordEntryBudget];positivity
  have hCN : 0 ≤ CN := by dsimp only [CN];positivity
  have hBW : 0 ≤ BW := by
    have hD := principalModelDegreeCoordinateBudget_nonneg K (M ⟨1,by omega⟩) (Cj 2) (zero_le_one.trans hK)
    have hE := principalFirstErrorCoordinateTwoJetBudget_nonneg K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
      (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _)
    dsimp only [BW]
    positivity
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖firstPotentialCubicComplexDensity P W E y‖ ≤
      (CC*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    let β := beta d.γ d.radius y
    have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
    have hPoint (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y) :
        |firstPotentialCubicDensity P W U y| ≤ (2*BW*CN*ε^2)*(metricDensity d.γ y*∑ b : I,
          halfCovariantDirectionEnergy d (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b)) := by
      have hUD := (hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
      have hRow (b : I) :
          |∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a*
            sphereSobolevDualPairing (1/2:ℝ)
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (firstSelfSourceDerivative d U y (axis b)))
              (firstPotentialNormalizedCubic P (W y hy) a (PhysicalPrincipalData.potentialWordCoefficient d y)
                (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))| ≤
          (BW*CN)*ε^2*halfCovariantDirectionEnergy d
            (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b) := by
        have hh := firstPotential_cubic_row_point_bound hm hY P hd hK hf hε hε1 hy hCG hCK (W y hy) b
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) (firstSelfSourceDerivative d U y (axis b))
        simpa only [firstSelfSourceDerivative_inclusion d U hUD,halfCovariantDirectionEnergy,BW,CN,CQ,G,β] using hh
      unfold firstPotentialCubicDensity
      rw [dite_eq_left hy,abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) hμ)]
      calc
        _ ≤ (2*metricDensity d.γ y)*(∑ b : I,|∑ a : PhysicalPotentialGeneratorIndex,
            effectiveFirstWordCoefficient d b y a*sphereSobolevDualPairing (1/2:ℝ)
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (firstSelfSourceDerivative d U y (axis b)))
              (firstPotentialNormalizedCubic P (W y hy) a (PhysicalPrincipalData.potentialWordCoefficient d y)
                (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))|) :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (by norm_num) hμ)
        _ ≤ (2*metricDensity d.γ y)*(∑ b : I,(BW*CN)*ε^2*halfCovariantDirectionEnergy d
            (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun b _ => hRow b)) (mul_nonneg (by norm_num) hμ)
        _ = _ := by rw [←Finset.mul_sum];ring
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
    unfold firstPotentialCubicComplexDensity
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hR hI
      _ = (2*BW*CN*ε^2)*(metricDensity d.γ y*((∑ b : I,halfCovariantDirectionEnergy d
          (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))+
          ∑ b : I,halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis b))) := by ring
      _ ≤ (2*BW*CN*ε^2)*((3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
        mul_le_mul_of_nonneg_left hEnergy (by positivity)
      _ = _ := by dsimp only [CC];ring
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (CC*ε^2)
  have hN := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hN

end ShrinkingSpheres.ParallelEnergy
