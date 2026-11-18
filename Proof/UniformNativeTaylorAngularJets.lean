import Proof.NativeFullRadialAngularRegularity
import Proof.UniformNativeRelativeSymmetricHigherData
import Proof.UniformRelativeAngularDerivativeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Extract the shared Taylor angular-field estimate before weakening its
    quadratic radius gain for the full radial operator. -/
theorem uniform_native_taylor_angular_field_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (_hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η BT : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ BT ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,
        CoarseAngularFields.JetBound s.response.adjointTaylorAngularFields
          ((y,frameVectorLinear d.frame y),0) 3 (BT*(d.radius y)^2) := by
  obtain ⟨η,CF,CA,hη,hη1,hCF,hCA,hHigher⟩ := uniform_native_relative_symmetric_higher_data hY hΩ 4
    (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨CG,hCG,hAngular⟩ := uniform_relative_angular_derivative_higher_jets
    (E := SphereSobolev 1 →L[ℝ] SphereSobolev 0) hΩ 3 (by omega) K M hK
  let BT := CF+CA+CG*(CF+CA)
  have hCF0 := zero_le_one.trans hCF
  have hCA0 := zero_le_one.trans hCA
  have hCG0 := zero_le_one.trans hCG
  have hBT : 0 ≤ BT := by dsimp only [BT];positivity
  have hFB : CF ≤ BT := by dsimp only [BT];nlinarith only [hCA0,mul_nonneg hCG0 (add_nonneg hCF0 hCA0)]
  have hAB : CA ≤ BT := by dsimp only [BT];nlinarith only [hCF0,mul_nonneg hCG0 (add_nonneg hCF0 hCA0)]
  have hCFB : CG*CF ≤ BT := by dsimp only [BT];nlinarith only [hCF0,hCA0,mul_nonneg hCG0 hCA0]
  have hCAB : CG*CA ≤ BT := by dsimp only [BT];nlinarith only [hCF0,hCA0,mul_nonneg hCG0 hCF0]
  refine ⟨η,BT,hη,hη1,hBT,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨H⟩ := hHigher floor hf ε hε hSmall d hd y hy CQ CF0 CA0 CM s
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using
      hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hForward := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hd.2.1.center_mem hy)
    (frameVectorLinear d.frame y) he s.response.forwardTaylor s.response.contDiffAt_forwardTaylor
    (CF*(d.radius y)^2) (by positivity) H.forwardJets
  have hAdjoint := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hd.2.1.center_mem hy)
    (frameVectorLinear d.frame y) he s.response.adjointTaylor s.response.contDiffAt_adjointTaylor
    (CA*(d.radius y)^2) (by positivity) H.adjointJets
  refine ⟨H.neighborhood,⟨⟨by positivity,s.response.contDiffAt_adjointTaylor,?_⟩,
    ⟨by positivity,s.response.contDiffAt_forwardTaylor,?_⟩,?_,?_⟩⟩
  · intro n hn
    exact (H.adjointJets n (by omega)).trans (mul_le_mul_of_nonneg_right hAB (sq_nonneg _))
  · intro n hn
    exact (H.forwardJets n (by omega)).trans (mul_le_mul_of_nonneg_right hFB (sq_nonneg _))
  · intro ij
    refine ⟨by positivity,(hAdjoint ij.1 ij.2).1,?_⟩
    intro n hn
    exact ((hAdjoint ij.1 ij.2).2 n hn).trans
      (by calc
        CG*(CA*(d.radius y)^2) = (CG*CA)*(d.radius y)^2 := by ring
        _ ≤ BT*(d.radius y)^2 := mul_le_mul_of_nonneg_right hCAB (sq_nonneg _))
  · intro ij
    refine ⟨by positivity,(hForward ij.1 ij.2).1,?_⟩
    intro n hn
    exact ((hForward ij.1 ij.2).2 n hn).trans
      (by calc
        CG*(CF*(d.radius y)^2) = (CG*CF)*(d.radius y)^2 := by ring
        _ ≤ BT*(d.radius y)^2 := mul_le_mul_of_nonneg_right hCFB (sq_nonneg _))
end ShrinkingSpheres
