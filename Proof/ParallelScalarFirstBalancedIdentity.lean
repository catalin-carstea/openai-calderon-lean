import Proof.ParallelScalarFirstHighSections
import Proof.EffectiveFirstAdjointBalancedDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- Exact paired scalar/first identity at genuine half-order endpoints.
The second summand has the plus sign forced by the negative divergence
in the true physical first adjoint. The scalar transpose representative
uses precisely the supplied scalar adjoint defect. -/
theorem scalarFirstDensity_balanced_identity
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    {y : X} (hy : y ∈ Y) :
    let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
    let S := scalarFiveHalfSecondSection d A U y
    let R := S+scalarFiveHalfDefectSection d (metricDensity d.γ) A U y
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    scalarFirstDensity P WF W U y=
      2*(metricDensity d.γ y*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
          (P.firstCovariantCoordinateHalfL b y (J (fiveHalfCovariantDerivative d U (axis b) y))))+
        ∑ b : I,sphereSobolevDualPairing (1/2:ℝ) R (P.firstAdjointBalancedDensityRow WF U b y)) := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let S := scalarFiveHalfSecondSection d A U y
  let R := S+scalarFiveHalfDefectSection d (metricDensity d.γ) A U y
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y :=
    (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hS : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) S=
      scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y :=
    scalarFiveHalfSecondSection_inclusion hY d hg hK he A U hU hy
  have hTranspose := scalarCovariantSecondTransposeSection_eq_add_defect hY d hg hK he
    (metricDensity d.γ) (hg.contDiffOn_density hK) A
    (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK)
    (fun x hx => (hd.principal_properties hK (hSub hx)).1.isHermitian.smul (by simp [isSelfAdjoint_iff]))
    (fiveHalfToTwoSection U) hU2.contDiffOn hy (metricDensity_pos hg hK hy).ne'
  have hR : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) R=
      scalarCovariantSecondTransposeSection d (metricDensity d.γ) A (fiveHalfToTwoSection U) y := by
    rw [show R=S+scalarFiveHalfDefectSection d (metricDensity d.γ) A U y from rfl,map_add,hS,
      scalarFiveHalfDefectSection_inclusion d _ A U hU y]
    exact hTranspose.symm
  have hForward (b : I) :
      ⟪scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y,
        P.firstCovariantCoreRow (fiveHalfToTwoSection U) b y⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) S
        (P.firstCovariantCoordinateHalfL b y (J (fiveHalfCovariantDerivative d U (axis b) y))) := by
    have hCoarse := DFunLike.congr_fun (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b)
      (highSectionCovariantDerivative d (fiveHalfToTwoSection U) y (axis b))
    simp only [ContinuousLinearMap.comp_apply] at hCoarse
    have hD := congrArg (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
      (fiveHalfCovariantDerivative_inclusion d U y (axis b) (hU.differentiable (by simp) y))
    simp only [sphereSobolevInclusionL_trans_apply] at hD
    rw [←hD] at hCoarse
    have hPair := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) S
      (P.firstCovariantCoreRow (fiveHalfToTwoSection U) b y)
    change sphereSobolevDualPairing (1/2:ℝ) S
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (P.firstCovariantCoreRow (fiveHalfToTwoSection U) b y))=_ at hPair
    dsimp only [PhysicalPrincipalData.firstCovariantCoreRow] at hPair
    rw [hCoarse,hS] at hPair
    exact hPair.symm
  have hAdjoint (b : I) :
      metricDensity d.γ y*⟪scalarCovariantSecondTransposeSection d (metricDensity d.γ) A
        (fiveHalfToTwoSection U) y,P.firstFormalAdjointCoreRow WF W U b y⟫_ℝ=
      -sphereSobolevDualPairing (1/2:ℝ) R (P.firstAdjointBalancedDensityRow WF U b y) := by
    have hBalanced := P.firstAdjointDensityCoreRow_balanced_graph hY hΩ hd hK WF W U hU.contDiffOn b
      (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b) hy
    have hPair := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) R
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstAdjointDensityCoreRow WF W U b y))
    simp only [sphereSobolevInclusionL_trans_apply,hBalanced,hR] at hPair
    calc
      _ = ⟪scalarCovariantSecondTransposeSection d (metricDensity d.γ) A (fiveHalfToTwoSection U) y,
          metricDensity d.γ y • P.firstFormalAdjointCoreRow WF W U b y⟫_ℝ :=
        (real_inner_smul_right _ _ _).symm
      _ = -⟪scalarCovariantSecondTransposeSection d (metricDensity d.γ) A (fiveHalfToTwoSection U) y,
          sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.firstAdjointDensityCoreRow WF W U b y)⟫_ℝ := by
        rw [P.firstFormalAdjointCoreRow_density WF W U b (metricDensity_pos hg hK hy).ne',inner_neg_right]
      _ = _ := congrArg Neg.neg hPair.symm
  have hForwardSum :
      ⟪scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y,
        P.firstCovariantCoreSection (fiveHalfToTwoSection U) y⟫_ℝ=
      ∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
        (P.firstCovariantCoordinateHalfL b y (J (fiveHalfCovariantDerivative d U (axis b) y))) := by
    simp only [PhysicalPrincipalData.firstCovariantCoreSection,inner_sum,hForward]
  have hAdjointSum :
      metricDensity d.γ y*⟪scalarCovariantSecondTransposeSection d (metricDensity d.γ) A
        (fiveHalfToTwoSection U) y,P.firstFormalAdjointCore WF W U y⟫_ℝ=
      -(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) R (P.firstAdjointBalancedDensityRow WF U b y)) := by
    simp only [PhysicalPrincipalData.firstFormalAdjointCore,inner_sum,Finset.mul_sum,hAdjoint,
      Finset.sum_neg_distrib]
  change 2*metricDensity d.γ y*
    (⟪scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y,
        P.firstCovariantCoreSection (fiveHalfToTwoSection U) y⟫_ℝ-
      ⟪scalarCovariantSecondTransposeSection d (metricDensity d.γ) A (fiveHalfToTwoSection U) y,
        P.firstFormalAdjointCore WF W U y⟫_ℝ)=_
  rw [hForwardSum]
  linear_combination -2*hAdjointSum

end ShrinkingSpheres.ParallelEnergy
