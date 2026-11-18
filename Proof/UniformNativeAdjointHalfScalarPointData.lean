import Proof.UniformNativeAdjointHalfScalarNeighborhoodData
import Proof.NativeAdjointHalfScalarCommutator
import Proof.DenseSkewAdjoint
import Proof.NativeAntisymmetricTaylorNeighborhood
import Proof.NativeAntisymmetricKernelRegularity
import Proof.ZeroOrderInterpolationJets
import Proof.UniformNativeAntisymmetricTaylorData
import Proof.SmoothFiniteAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
local instance nativeAdjointHalfScalarPointNegativeComplete : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := lp.completeSpace

/-- A common native skew witness supplies every closed scalar adjoint
commutator at the actual native basepoint, with quadratic gained joint three-jets.
Neighborhood physical identification is not asserted by this point producer. -/
theorem uniform_native_adjoint_half_scalar_point_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    ∃ η CK CJ : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧ 0 ≤ CJ ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ V : s.response.SymmetricAdjointDomain,
      ∃ KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        SmoothFiniteJetBound KN ((y,frameVectorLinear d.frame y),0) 3 (CK*(d.radius y)^2) ∧
        (∀ T : NormalFrameRelativeParameter → ClosedCoefficientJets 3,∀ BT : ℝ,
          SmoothFiniteJetBound T ((y,frameVectorLinear d.frame y),0) 3 BT →
          SmoothFiniteJetBound (fun p => s.response.adjointHalfScalarCommutator F0 KN (T p) p)
            ((y,frameVectorLinear d.frame y),0) 3 ((CJ*BT)*(d.radius y)^2)) ∧
        ∀ T : ClosedCoefficientJets 3,
          let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            ((s.response.adjointHalfScalarCommutator F0 KN T p).comp
              (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=
                (s.response.adjointTaylor p).comp (closedOneBoundaryScalarMultiplierL T)-
                  (closedThreeJetCoarseScalarMultiplierL T).comp (s.response.adjointTaylor p) ∧
          (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num) p).comp
            (closedThreeJetHigherScalarMultiplierL T)-
            (closedThreeJetHalfBoundaryScalarMultiplierL T).comp
              (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num) p)=
                (s.response.adjointHalfScalarCommutator F0 KN T p).comp
                  (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  obtain ⟨η,CK,CJ,hη,hη1,hCK,hCJ,hProduce⟩ := uniform_native_adjoint_half_scalar_neighborhood_data
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q hQ
  refine ⟨η,CK,CJ,hη,hη1,hCK,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨A⟩ := hProduce floor hf ε hε hSmall d hd y hy CF CA CM s
  refine ⟨A.domain,A.kernel,A.kernel_jets,A.scalar_jets,?_⟩
  intro T
  exact ⟨A.low_graph _ A.pointMem T,A.high_graph _ A.pointMem T⟩
end ShrinkingSpheres
