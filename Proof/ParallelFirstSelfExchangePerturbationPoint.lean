import Proof.ParallelFirstSelfActualHodgeIntegral
import Proof.ParallelFirstSelfSourceEnergyPoint
import Proof.ParallelFirstSelfMatrixPerturbation
import Proof.ParallelFirstSelfLeadingExchange

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

private lemma matrix_exchange_eq_cross_sub_norm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : I → I → F) : firstSelfMatrixExchange A=
      (∑ b : I,∑ c : I,⟪A b c,A c b⟫_ℝ)-‖∑ b : I,A b b‖^2 := by
  unfold firstSelfMatrixExchange
  rw [←real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

lemma firstSelfExchangeDensity_eq_matrix_exchange {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    firstSelfExchangeDensity WF U y=metricDensity d.γ y*firstSelfMatrixExchange
      (fun b i => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis i)))) := by
  let A := fun b i => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis i)))
  have hL : firstAdjointLeadingCoreSection WF U y=-(∑ b : I,A b b) := by
    unfold firstAdjointLeadingCoreSection firstAdjointLeadingCoreRow
    change (∑ b : I,-A b b)=-(∑ b : I,A b b)
    rw [Finset.sum_neg_distrib]
  rw [matrix_exchange_eq_cross_sub_norm]
  unfold firstSelfExchangeDensity firstSelfCrossedAdjointDensity
  rw [hL,norm_neg]
  dsimp only [A]
  ring

lemma firstSelfAdjointSourceHodgeDensity_eq_matrix_exchange (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    firstSelfAdjointSourceHodgeDensity P WF W U y=metricDensity d.γ y*firstSelfMatrixExchange
      (fun b i => sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (firstSelfAdjointSourceDerivative P WF W U b i y)) := by
  unfold firstSelfAdjointSourceHodgeDensity balancedHalfHodgePairDensity firstSelfMatrixExchange
    firstSelfAdjointSourceDerivative
  simp only [Finset.mul_sum]

/-- Exact complete exchange perturbation bound. Every physical pairing
uses the positive-half error against the genuine weak derivative. -/
theorem first_self_exchange_hodge_perturbation_point_bound
    {CA CL CJ β : ℝ} (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (hPoint : FirstSelfAdjointSourcePointBounds P WF W U y CA CL CJ)
    (hCL : 0 ≤ CL) (hCJ : 0 ≤ CJ) (hε : 0 ≤ ε) (hβ : 1 ≤ β) :
    |firstSelfExchangeDensity WF U y-firstSelfAdjointSourceHodgeDensity P WF W U y| ≤
      (54*CJ*(CL+CJ))*ε^2*metricDensity d.γ y*
        ∑ j : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis j) := by
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let E := ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j)
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let G := fun b i => Z (firstSelfAdjointSourceDerivative P WF W U b i y)
  let T := fun b i => Z (firstSelfAdjointSourceJetError P WF W U b i y)
  have hPair := first_self_adjoint_source_error_pair_bounds P WF W U hy hPoint hCL hCJ hε hβ
  have hBound := firstSelfMatrixExchange_sub_bound G T ((CJ*(CL+CJ))*ε^2*E) hPair.1 hPair.2
  have hA : (fun b i => Z (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis i))))=
      (fun b i => G b i-T b i) := by
    funext b i
    dsimp only [G,T,firstSelfAdjointSourceJetError]
    rw [map_sub]
    abel
  rw [firstSelfExchangeDensity_eq_matrix_exchange,firstSelfAdjointSourceHodgeDensity_eq_matrix_exchange]
  change |metricDensity d.γ y*firstSelfMatrixExchange
      (fun b i => Z (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis i))))-
    metricDensity d.γ y*firstSelfMatrixExchange G| ≤ _
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  rw [hA,←mul_sub,abs_mul,abs_of_nonneg hμ]
  exact (mul_le_mul_of_nonneg_left hBound hμ).trans_eq (by dsimp only [E,V];ring)

end ShrinkingSpheres.ParallelEnergy
