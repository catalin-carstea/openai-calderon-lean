import Proof.ParallelScalarFirstBalancedIdentity
import Proof.ParallelScalarFirstPairAlgebra

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

/-- Both first orientations are combined into the genuinely symmetric
coefficient B+B*. The other terms use the actual covariant coefficient
derivative, relative density derivative, and scalar adjoint defect. -/
theorem scalarFirstDensity_symmetric_expansion
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
    let F := scalarFiveHalfDefectSection d (metricDensity d.γ) A U y
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let L := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
    let U0 := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y)
    scalarFirstDensity P WF W U y=
      2*(metricDensity d.γ y*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
          ((P.firstCovariantCoordinateHalfL b y+(P.firstCovariantCoordinateHalfL b y).adjoint)
            (J (fiveHalfCovariantDerivative d U (axis b) y))))+
        (∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
          (metricDensity d.γ y • WF.covariantCoordinateAdjointDerivative b b y L+
            fderiv ℝ (metricDensity d.γ) y (axis b) • (P.firstCovariantCoordinateHalfL b y).adjoint U0))+
        ∑ b : I,sphereSobolevDualPairing (1/2:ℝ) F (P.firstAdjointBalancedDensityRow WF U b y)) := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let S := scalarFiveHalfSecondSection d A U y
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) A U y
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let L := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let U0 := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y)
  have hBalanced (b : I) : P.firstAdjointBalancedDensityRow WF U b y=
      metricDensity d.γ y • ((P.firstCovariantCoordinateHalfL b y).adjoint
        (J (fiveHalfCovariantDerivative d U (axis b) y))+
        WF.covariantCoordinateAdjointDerivative b b y L)+
      fderiv ℝ (metricDensity d.γ) y (axis b) • (P.firstCovariantCoordinateHalfL b y).adjoint U0 := by
    dsimp only [PhysicalPrincipalData.firstAdjointBalancedDensityRow]
    rw [←fiveHalfCovariantDerivative_half_inclusion d U y (axis b) (hU.differentiable (by simp) y)]
  have hId := scalarFirstDensity_balanced_identity hY hΩ hSub hd hK P WF W U hU hy
  change scalarFirstDensity P WF W U y=2*(metricDensity d.γ y*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
    (P.firstCovariantCoordinateHalfL b y (J (fiveHalfCovariantDerivative d U (axis b) y))))+
      ∑ b : I,sphereSobolevDualPairing (1/2:ℝ) (S+F) (P.firstAdjointBalancedDensityRow WF U b y)) at hId
  change scalarFirstDensity P WF W U y=
    2*(metricDensity d.γ y*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
          ((P.firstCovariantCoordinateHalfL b y+(P.firstCovariantCoordinateHalfL b y).adjoint)
            (J (fiveHalfCovariantDerivative d U (axis b) y))))+
        (∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
          (metricDensity d.γ y • WF.covariantCoordinateAdjointDerivative b b y L+
            fderiv ℝ (metricDensity d.γ) y (axis b) • (P.firstCovariantCoordinateHalfL b y).adjoint U0))+
        ∑ b : I,sphereSobolevDualPairing (1/2:ℝ) F (P.firstAdjointBalancedDensityRow WF U b y))
  exact hId.trans (scalar_first_symmetric_split_algebra
    (metricDensity d.γ y) S F U0 (fun b => P.firstCovariantCoordinateHalfL b y)
    (fun b => J (fiveHalfCovariantDerivative d U (axis b) y))
    (fun b => WF.covariantCoordinateAdjointDerivative b b y L)
    (fun b => fderiv ℝ (metricDensity d.γ) y (axis b))
    (fun b => P.firstAdjointBalancedDensityRow WF U b y) hBalanced)

end ShrinkingSpheres.ParallelEnergy
