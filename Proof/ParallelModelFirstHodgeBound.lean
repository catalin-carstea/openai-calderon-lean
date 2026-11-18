import Proof.ParallelModelFirstLeadingPoint
import Proof.ParallelModelFirstWeights

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME-WF mixed Hodge curvature/density remainder has a linear
energy bound; the background model adjoint carries no epsilon factor. -/
theorem model_first_actual_hodge_remainder_point_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK R0 CA CL CJ Q1 CQ : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hR0 : 0 ≤ R0) (hCA : 0 ≤ CA) (hCL : 0 ≤ CL) (hCJ : 0 ≤ CJ)
    (hQ1 : 0 ≤ Q1) (hCQ : 0 ≤ CQ) (hε : 0 ≤ ε)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (hR : ∀ c,‖scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y‖ ≤ R0)
    (hPoint : FirstSelfAdjointSourcePointBounds P WF W U y CA CL CJ)
    (hQ : ∀ k c,|modelFirstLeadingWeight d k c y| ≤ K*metricDensity d.γ y ∧
      ∀ i,|fderiv ℝ (modelFirstLeadingWeight d k c) y (axis i)| ≤ Q1*metricDensity d.γ y)
    (hCurv : ∀ k b,‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis k) (axis b)‖ ≤ CQ) :
    |modelFirstHodgeRemainder WF U y| ≤
      (27*R0*(K*CQ*(CA+CL)+2*Q1*(2*(CA+CL)+CJ)))*ε*metricDensity d.γ y*
        ∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i) := by
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let β := beta d.γ d.radius y
  let En := ∑ i : I,halfCovariantDirectionEnergy d U3 y β (axis i)
  let v := fun i : I => ‖halfSectionCovariantDerivativeL d U3 y (axis i)‖
  let C := R0*(K*CQ*(CA+CL)+2*Q1*(2*(CA+CL)+CJ))
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hEn := model_first_component_energy_controls d U3 y β hβ
  have hSource (c : I) : ‖modelFirstRaisingAdjointSource d U c y‖ ≤ R0*‖U3 y‖ :=
    ((scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hR c) (norm_nonneg _))
  have hBSource (b : I) : ‖WF.covariantAdjointLowSection U b y‖ ≤ (CA+CL)*ε*‖U3 y‖ :=
    (hPoint.source b).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCL) hε) (norm_nonneg _))
  have hWeak (b i : I) : ‖weakHalfSourceCovariantDerivative d (WF.covariantAdjointLowSection U b) y (axis i)‖ ≤
      ε*((CA+CL)*v i+CJ*‖U3 y‖) := by
    apply (hPoint.weak b i).trans
    apply mul_le_mul_of_nonneg_left _ hε
    exact add_le_add (mul_le_mul_of_nonneg_right
      (show CL ≤ CA+CL by linarith only [hCA]) (norm_nonneg _)) (le_refl _)
  have hEach (k c b : I) : |balancedHalfHodgePairRemainder d (modelFirstLeadingWeight d k c)
      (modelFirstRaisingAdjointSource d U c) (WF.covariantAdjointLowSection U b) (axis k) (axis b) y| ≤
      C*ε*metricDensity d.γ y*En :=
    model_first_hodge_remainder_point_bound d (modelFirstLeadingWeight d k c) _ _ y k b
      R0 (CA+CL) CJ K Q1 CQ ε β (metricDensity d.γ y) ‖U3 y‖ En
      hR0 (add_nonneg hCA hCL) hCJ (zero_le_one.trans hK) hQ1 hCQ hε hβ (Real.sqrt_nonneg _) (norm_nonneg _)
      (hQ k c).1 (hQ k c).2 (hSource c) (hBSource b) (hCurv k b) v (fun _ => norm_nonneg _)
      (hWeak b) hEn.1 hEn.2
  unfold modelFirstHodgeRemainder
  have hSum := abs_fin_three_sum_le _ _ (fun k => abs_fin_three_sum_le _ _ (fun c => abs_fin_three_sum_le _ _ (hEach k c)))
  exact hSum.trans_eq (by dsimp only [C,En,U3,β];ring)

end ShrinkingSpheres.ParallelEnergy
