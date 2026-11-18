import Proof.NativeScalarOperatorFamily
import Proof.UniformRelativeAngularDerivativeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A shared selected physical neighborhood and gained operator-angular
    two-jets, before choosing any coefficient family. -/
theorem uniform_native_scalar_angular_operator_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ))) :
    ∃ η CK CJ CG : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧ 0 ≤ CJ ∧ 1 ≤ CG ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ A : NativeAdjointHalfScalarNeighborhoodData s hd.1.1 (zero_lt_one.trans_le hK) CK CJ,
        ∀ i j,SmoothFiniteJetBound
          (normalFrameRelativeAngularDerivative d.γ A.scalarOperatorFamily i j)
          ((y,frameVectorLinear d.frame y),0) 2 (CG*(CJ*(d.radius y)^2)) := by
  obtain ⟨η,CK,CJ,hη,hη1,hCK,hCJ,hNeighborhood⟩ := uniform_native_adjoint_half_scalar_neighborhood_data
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  obtain ⟨CG,hCG,hAngular⟩ := uniform_relative_angular_derivative_higher_jets
    (E:=ClosedCoefficientJets 3 →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)))
    hΩ 2 (by omega) K M hK
  refine ⟨η,CK,CJ,CG,hη,hη1,hCK,hCJ,hCG,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨A⟩ := hNeighborhood floor hf ε hε hSmall d hd y hy CF CA CM s
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hS := A.scalarOperatorFamily_three_jets hCJ
  have hAng := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hd.2.1.center_mem hy) (frameVectorLinear d.frame y) he
    A.scalarOperatorFamily hS.smooth (CJ*(d.radius y)^2) hS.nonneg hS.bound
  exact ⟨A,fun i j => ⟨mul_nonneg (zero_le_one.trans hCG) hS.nonneg,(hAng i j).1,(hAng i j).2⟩⟩
end ShrinkingSpheres
