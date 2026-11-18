import Proof.ParallelFirstSelfActualHodgeIntegral
import Proof.ParallelFirstSelfSourceEnergyPoint

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

/-- The actual curvature/density Hodge remainder is controlled in the
original weak-gradient energy, using only reference curvature and density. -/
theorem first_self_hodge_remainder_point_bound
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε CA CL CJ MQ CR β : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (hPoint : FirstSelfAdjointSourcePointBounds P WF W U y CA CL CJ)
    (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hCJ : 0 ≤ CJ) (hMQ : 0 ≤ MQ) (hCR : 0 ≤ CR)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hDμ : ∀ i,|fderiv ℝ (metricDensity d.γ) y (axis i)| ≤ MQ*metricDensity d.γ y)
    (hCurv : ∀ b c,‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c)‖ ≤ CR) :
    |firstSelfAdjointSourceHodgeRemainder WF U y| ≤
      (9*(CA^2*CR+2*MQ*CA*(CL+CJ)))*ε^2*metricDensity d.γ y*
        ∑ j : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis j) := by
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let E := ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j)
  let L := fun b => WF.covariantAdjointLowSection U b y
  let R := fun c j => weakHalfSourceCovariantDerivative d (WF.covariantAdjointLowSection U c) y (axis j)
  let Q := CA^2*CR+2*MQ*CA*(CL+CJ)
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hm : ‖V y‖^2 ≤ E := first_self_mass_sq_le_total d V y hβ
  have hmg (j : I) : ‖V y‖*‖halfSectionCovariantDerivativeL d V y (axis j)‖ ≤ E :=
    first_self_mass_gradient_le_total d V y hβ j
  have hRV (b c j : I) : |sphereSobolevDualPairing (1/2:ℝ) (L b) (R c j)| ≤
      (CA*(CL+CJ))*ε^2*E := by
    calc
      _ ≤ ‖L b‖*‖R c j‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (CA*ε*‖V y‖)*(ε*(CL*‖halfSectionCovariantDerivativeL d V y (axis j)‖+CJ*‖V y‖)) :=
        mul_le_mul (hPoint.source b) (hPoint.weak c j) (norm_nonneg _) (by positivity)
      _ = (CA*CL*ε^2)*(‖V y‖*‖halfSectionCovariantDerivativeL d V y (axis j)‖)+
          (CA*CJ*ε^2)*‖V y‖^2 := by ring
      _ ≤ (CA*CL*ε^2)*E+(CA*CJ*ε^2)*E := add_le_add
        (mul_le_mul_of_nonneg_left (hmg j) (by positivity)) (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = _ := by ring
  have hRC (b c : I) : |sphereSobolevDualPairing (1/2:ℝ) (L b)
      (frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c) (L c))| ≤ (CA^2*CR)*ε^2*E := by
    have hC : ‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c) (L c)‖ ≤ CR*(CA*ε*‖V y‖) :=
      ((frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c)).le_opNorm (L c)).trans
        (mul_le_mul (hCurv b c) (hPoint.source c) (norm_nonneg _) hCR)
    calc
      _ ≤ ‖L b‖*‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis b) (axis c) (L c)‖ :=
        abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (CA*ε*‖V y‖)*(CR*(CA*ε*‖V y‖)) := mul_le_mul (hPoint.source b) hC (norm_nonneg _) (by positivity)
      _ = ((CA^2*CR)*ε^2)*‖V y‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have hPair (b c : I) : |balancedHalfHodgePairRemainder d (metricDensity d.γ)
      (WF.covariantAdjointLowSection U b) (WF.covariantAdjointLowSection U c) (axis b) (axis c) y| ≤
      Q*ε^2*metricDensity d.γ y*E := by
    unfold balancedHalfHodgePairRemainder
    refine ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
    simp only [abs_mul,abs_of_nonneg hμ]
    have h1 := mul_le_mul_of_nonneg_left (hRC b c) hμ
    have h2 := mul_le_mul (hDμ b) (hRV b c c) (abs_nonneg _) (mul_nonneg hMQ hμ)
    have h3 := mul_le_mul (hDμ c) (hRV b c b) (abs_nonneg _) (mul_nonneg hMQ hμ)
    exact (add_le_add (add_le_add h1 h2) h3).trans_eq (by dsimp only [Q];ring)
  unfold firstSelfAdjointSourceHodgeRemainder
  calc
    _ ≤ ∑ b : I,∑ c : I,|balancedHalfHodgePairRemainder d (metricDensity d.γ)
        (WF.covariantAdjointLowSection U b) (WF.covariantAdjointLowSection U c) (axis b) (axis c) y| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _b : I,∑ _c : I,Q*ε^2*metricDensity d.γ y*E :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ => hPair b c))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];dsimp only [Q,E,V];ring

end ShrinkingSpheres.ParallelEnergy
