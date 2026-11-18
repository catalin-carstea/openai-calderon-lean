import Proof.ParallelFirstPotentialRow
import Proof.ParallelFirstPotentialGreenWeight

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstPotentialPairedDensity (P : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ b : I,∑ a : PhysicalPotentialGeneratorIndex,quadraticHigherPairDensity d (firstPotentialGreenWeight d b a)
    (fun x => normalizedPotentialGeneratorHigh P x a) P.potentialQuadraticHalfL U (axis b) y

def firstPotentialBoundedDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*metricDensity d.γ y*∑ b : I,
    (⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (firstPotentialBoundedForwardHigherL d b y (firstSelfSourceDerivative d U y (axis b))),P.potentialQuadraticCoreSection W U y⟫_ℝ+
     ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (effectiveFirstBoundedAdjointHigherL d b y (firstSelfSourceDerivative d U y (axis b))),P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ)

def firstPotentialCubicDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  by
  classical
  exact if hy : y ∈ Y then 2*metricDensity d.γ y*∑ b : I,∑ a : PhysicalPotentialGeneratorIndex,
    effectiveFirstWordCoefficient d b y a*sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (firstSelfSourceDerivative d U y (axis b)))
      (firstPotentialNormalizedCubic P (W y hy) a (PhysicalPrincipalData.potentialWordCoefficient d y)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))) else 0

private lemma firstPotential_finite_split {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ℝ) (w F G C : ι → κ → ℝ) (R A : ι → ℝ) :
    2*μ*(∑ b,((∑ a,w b a*(F b a+G b a-C b a))+R b+A b))=
      (∑ b,∑ a,(2*μ*w b a)*(F b a+G b a))+
      2*μ*(∑ b,(R b+A b))-2*μ*(∑ b,∑ a,w b a*C b a) := by
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    Finset.mul_sum,mul_assoc]
  ring

/-- Exact raw-sector splitting into paired Green, bounded order-zero,
order-dropped angular cubic, and the complete actual adjoint defect. -/
theorem firstPotentialDensity_exact_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    firstPotentialDensity P WF W U y=firstPotentialPairedDensity P U y+
      firstPotentialBoundedDensity P W U y-firstPotentialCubicDensity P W U y-
      firstPotentialDefectDensity P WF W U y := by
  let V := fun b : I => firstSelfSourceDerivative d U y (axis b)
  have hH (b : I) := P.firstCovariantCoordinateHigherL_balanced b y (hRaw b)
  have hRow (b : I) : P.firstCovariantCoreRow (fiveHalfToTwoSection U) b y=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstCovariantCoordinateHigherL b y (V b)) := by
    have hHigh := balanced_endpoint_high_of_coarse_low _ _ _
      (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b) (hH b)
    have hPoint := DFunLike.congr_fun hHigh (V b)
    simp only [ContinuousLinearMap.comp_apply] at hPoint
    unfold PhysicalPrincipalData.firstCovariantCoreRow
    rw [←firstSelfSourceDerivative_to_one d U hU]
    exact hPoint.symm
  have hSum : P.firstCovariantCoreSection (fiveHalfToTwoSection U) y=
      ∑ b : I,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstCovariantCoordinateHigherL b y (V b)) :=
    Finset.sum_congr rfl (fun b _ => hRow b)
  have hPair (b : I) := firstPotential_coefficient_row_pair hY hd P WF hy (W y hy) b (hRaw b) (U y) (V b)
  dsimp only [V] at hPair hSum
  have hQP : P.potentialQuadraticCoreSection W U y=P.potentialQuadraticCoreL (W y hy) (U y) := by
    simp only [PhysicalPrincipalData.potentialQuadraticCoreSection,dif_pos hy]
  have hQA : P.potentialQuadraticAdjointCoreSection W U y=P.potentialQuadraticAdjointCoreL (W y hy) (U y) := by
    simp only [PhysicalPrincipalData.potentialQuadraticAdjointCoreSection,dif_pos hy]
  have hLeading : firstPotentialLeadingDensity P WF W U y=
      firstPotentialPairedDensity P U y+firstPotentialBoundedDensity P W U y-firstPotentialCubicDensity P W U y := by
    rw [firstPotentialLeadingDensity_eq_positive_rows,hSum]
    simp only [sum_inner,←Finset.sum_add_distrib,hQP,hQA]
    simp only [hPair]
    dsimp only [firstPotentialPairedDensity,firstPotentialBoundedDensity,firstPotentialCubicDensity]
    rw [dif_pos hy]
    simp only [quadraticHigherPairDensity,firstPotentialGreenWeight,←graded_covariant_derivative_five_half,
      firstSelfSourceDerivative,hQP,hQA]
    exact firstPotential_finite_split _ _ _ _ _ _ _
  rw [firstPotentialDensity_eq_leading_sub_defect,hLeading]

end ShrinkingSpheres.ParallelEnergy
