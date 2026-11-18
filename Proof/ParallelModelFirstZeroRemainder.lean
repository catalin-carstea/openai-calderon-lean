import Proof.ParallelModelFirstZeroGreen
import Proof.ParallelModelFirstLeadingPoint
import Proof.ParallelNormAssemblyReservedHigherGreenPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The generic paired quadratic remainder is used with its exact point
scales: background C/DQ, epsilon/beta H, epsilon N, beta/beta² weight jets. -/
lemma model_first_zero_quadratic_remainder_bound
    (q : X → ℝ) (H N : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C DQ : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (a y : X)
    (Q0 Q1 CA CJ CQ CD ε β μ : ℝ)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hCA : 0 ≤ CA) (hCJ : 0 ≤ CJ)
    (hCQ : 0 ≤ CQ) (hCD : 0 ≤ CD) (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ)
    (hq : |q y| ≤ Q0*β*μ) (hdq : |fderiv ℝ q y a| ≤ Q1*β^2*μ)
    (hH : ‖H y‖ ≤ CA*ε/β) (hN : ‖N y‖ ≤ CJ*ε)
    (hC : ‖C y‖ ≤ CQ) (hD : ‖DQ y‖ ≤ CD) :
    |quadraticHigherPairRemainder q H N C DQ U a y| ≤
      (Q0*(CJ*CQ+CA*CD)+Q1*CA*CQ)*ε*β*μ*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
  have hβp := zero_lt_one.trans_le hβ
  have hGen := quadratic_higher_pair_remainder_bound q H N C DQ U a y
    (Q0*β) (Q1*β^2) (CA*ε/β) (CJ*ε) CQ CD 1 1 μ
    (by positivity) (by positivity) (by positivity) (by positivity) hCQ hCD (by norm_num) (by norm_num) hμ hq hdq hH
    (by simpa only [mul_one] using hN) (by simpa only [mul_one] using hC)
    (by simpa only [mul_one] using hD)
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let B := Q0*(CJ*CQ+CA*CD)+Q1*CA*CQ
  calc
    _ ≤ ((Q0*β)*((CJ*ε)*CQ+(CA*ε/β)*CD)+(Q1*β^2)*(CA*ε/β)*CQ)*1*1*μ*‖u‖^2 := hGen
    _ = B*ε*β*μ*‖u‖^2-(Q0*CA*CD*ε*(β-1))*μ*‖u‖^2 := by
      dsimp only [B]
      field_simp [hβp.ne']
      ring
    _ ≤ B*ε*β*μ*‖u‖^2 := sub_le_self _ (by positivity)

/-- Exact actual zero-model paired remainder, measured in the original
half-gradient/H3/2-mass energy. The fixed first HIGH-jet witness is reused. -/
theorem model_first_zero_paired_remainder_point_bound
    {Y : Set X} {d : Data} {CF CT CB CS ε CE : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (hJ : FirstSelfCompleteAdjointJetBound WF CE) (U : X → SphereSobolev (5/2:ℝ))
    {y : X} (hy : y ∈ Y) (Q0 Q1 CA CQ CD β : ℝ)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hCQ : 0 ≤ CQ) (hCD : 0 ≤ CD) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hQ : ∀ k c,|modelFirstZeroWeight d k c y| ≤ Q0*β*metricDensity d.γ y ∧
      ∀ i,|fderiv ℝ (modelFirstZeroWeight d k c) y (axis i)| ≤ Q1*β^2*metricDensity d.γ y)
    (hH : ∀ b,‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε/β)
    (hC : ∀ c,‖modelFirstZeroAdjointWeakL d c y‖ ≤ CQ)
    (hD : ∀ c b,‖modelFirstZeroAdjointWeakJet d c b y‖ ≤ CD) :
    |modelFirstZeroPairedRemainder WF hJ U y| ≤
      (27*(Q0*(CE*CQ+CA*CD)+Q1*CA*CQ))*ε*metricDensity d.γ y*
        ∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y β (axis i) := by
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let En := ∑ i : I,halfCovariantDirectionEnergy d U3 y β (axis i)
  let B := Q0*(CE*CQ+CA*CD)+Q1*CA*CQ
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hMass := (model_first_component_energy_controls d U3 y β hβ).1
  have hEach (k c b : I) : |quadraticHigherPairRemainder (modelFirstZeroWeight d k c)
      (WF.covariantCoordinateAdjointHigher b) (modelFirstChosenAdjointJet WF hJ b b)
      (modelFirstZeroAdjointWeakL d c) (modelFirstZeroAdjointWeakJet d c b) U (axis b) y| ≤ B*ε*metricDensity d.γ y*En := by
    have hRaw := model_first_zero_quadratic_remainder_bound (modelFirstZeroWeight d k c)
      (WF.covariantCoordinateAdjointHigher b) (modelFirstChosenAdjointJet WF hJ b b)
      (modelFirstZeroAdjointWeakL d c) (modelFirstZeroAdjointWeakJet d c b) U (axis b) y
      Q0 Q1 CA CE CQ CD ε β (metricDensity d.γ y) hQ0 hQ1 hCA hCE hCQ hCD hε hβ (Real.sqrt_nonneg _)
      (hQ k c).1 ((hQ k c).2 b) (hH b) (modelFirstChosenAdjointJet_spec WF hJ b b hy).2 (hC c) (hD c b)
    calc
      _ ≤ (Q0*(CE*CQ+CA*CD)+Q1*CA*CQ)*ε*β*metricDensity d.γ y*
          ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := hRaw
      _ = (B*ε*metricDensity d.γ y)*(β*‖U3 y‖^2) := by dsimp only [B,U3];ring
      _ ≤ B*ε*metricDensity d.γ y*En := mul_le_mul_of_nonneg_left hMass
        (show 0 ≤ B*ε*metricDensity d.γ y from mul_nonneg (mul_nonneg hB hε) (Real.sqrt_nonneg _))
  unfold modelFirstZeroPairedRemainder
  have hSum := abs_fin_three_sum_le _ _ (fun k => abs_fin_three_sum_le _ _ (fun c => abs_fin_three_sum_le _ _ (hEach k c)))
  exact hSum.trans_eq (by dsimp only [B,En,U3];ring)

end ShrinkingSpheres.ParallelEnergy
