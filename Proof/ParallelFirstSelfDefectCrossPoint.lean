import Proof.ParallelFirstSelfCoreSplit
import Proof.HalfCovariantEnergyControl
import Proof.HalfScalarTransposeCompatibility

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
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

lemma firstAdjointLeadingCoreSection_weak_norm_le
    {P : PhysicalPrincipalData Y d CF CT} (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (hU : DifferentiableAt ℝ U y) {CL : ℝ}
    (hL : ∀ b,‖P.firstCovariantCoordinateHalfL b y‖ ≤ CL*ε) :
    ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (firstAdjointLeadingCoreSection WF U y)‖ ≤
      (CL*ε)*∑ b : I,‖halfSectionCovariantDerivativeL d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis b)‖ := by
  have hGraph : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (firstAdjointLeadingCoreSection WF U y)=∑ b : I,firstAdjointLeadingWeakRow P U b y := by
    unfold firstAdjointLeadingCoreSection
    rw [map_sum]
    exact Finset.sum_congr rfl (fun b _ => firstAdjointLeadingCoreRow_graph WF U hy hU b)
  rw [hGraph]
  calc
    _ ≤ ∑ b : I,‖firstAdjointLeadingWeakRow P U b y‖ := norm_sum_le _ _
    _ ≤ ∑ b : I,(CL*ε)*‖halfSectionCovariantDerivativeL d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis b)‖ :=
      Finset.sum_le_sum (fun b _ => by
        unfold firstAdjointLeadingWeakRow
        rw [norm_neg]
        exact (((P.firstCovariantCoordinateHalfL b y).adjoint).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hL b)
            (norm_nonneg _)))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Weak leading output pairs with the genuine positive-half defect.
Only the H1/2 covariant source derivative is estimated. -/
lemma first_self_defect_cross_inner_le
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (hU : DifferentiableAt ℝ U y) {CL CR β : ℝ}
    (hCL : 0 ≤ CL) (hCR : 0 ≤ CR) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hL : ∀ b,‖P.firstCovariantCoordinateHalfL b y‖ ≤ CL*ε)
    (R : SphereSobolev (1/2:ℝ))
    (hR : firstAdjointDefectCoreSection P WF W U y=sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) R)
    (hRN : ‖R‖ ≤ CR*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖) :
    |⟪firstAdjointLeadingCoreSection WF U y,firstAdjointDefectCoreSection P WF W U y⟫_ℝ| ≤
      (CR*CL)*ε^2*∑ b : I,halfCovariantDirectionEnergy d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis b) := by
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let G := fun b : I => halfSectionCovariantDerivativeL d V y (axis b)
  have hPair : ⟪firstAdjointLeadingCoreSection WF U y,firstAdjointDefectCoreSection P WF W U y⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) R (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (firstAdjointLeadingCoreSection WF U y)) := by
    rw [sphereSobolevDualPairing_zero_inclusion,hR,real_inner_comm]
  have hLN := firstAdjointLeadingCoreSection_weak_norm_le WF U hy hU hL
  have hProd : ‖V y‖*(∑ b : I,‖G b‖) ≤ ∑ b : I,halfCovariantDirectionEnergy d V y β (axis b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => by
      change ‖V y‖*‖G b‖ ≤ β⁻¹*‖G b‖^2+β*‖V y‖^2
      simpa only [mul_comm ‖V y‖] using weighted_product_le ‖G b‖ ‖V y‖ β hβ)
  rw [hPair]
  calc
    _ ≤ ‖R‖*‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (firstAdjointLeadingCoreSection WF U y)‖ := abs_sphereSobolevDualPairing_le _ _ _
    _ ≤ (CR*ε*‖V y‖)*((CL*ε)*∑ b : I,‖G b‖) :=
      mul_le_mul hRN hLN (norm_nonneg _) (by positivity)
    _ = ((CR*CL)*ε^2)*(‖V y‖*(∑ b : I,‖G b‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hProd (by positivity)

end ShrinkingSpheres.ParallelEnergy
