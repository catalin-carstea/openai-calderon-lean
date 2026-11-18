import Proof.NativeTaylorSelectedHigherJets
import Proof.UniformNativeSelectedDegreeJets
import Proof.NativeTaylorRotationHigherEndpoints
import Proof.UniformRelativeAngularDerivativeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2700
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Closed common genuine higher Taylor three-jets and SAME Taylor/rotation
commutator two-jets, with radius-squared gain, for ANY selected native domain. -/
theorem uniform_native_taylor_rotation_higher_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η CH : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ V : s.response.SymmetricAdjointDomain,
      V.TaylorRotationHigherJetBound hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)
        ((y,frameVectorLinear d.frame y),0) (CH*(d.radius y)^2) := by
  obtain ⟨η,CD,hη,hη1,hCD,hDegree⟩ := uniform_native_selected_degree_jets hY hΩ 3 (by omega)
    K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨CG,hCG,hAngular⟩ := uniform_relative_angular_derivative_higher_jets
    (E:=SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) hΩ 2 (by omega) K M hK
  let BL := |lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ|
  let BT := BL+CD
  let CH := 1+BT+CG*BT
  have hBL : 0 ≤ BL := abs_nonneg _
  have hCD0 : 0 ≤ CD := zero_le_one.trans hCD
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hBT : 0 ≤ BT := add_nonneg hBL hCD0
  have hCBT : 0 ≤ CG*BT := mul_nonneg hCG0 hBT
  have hCH : 1 ≤ CH := by dsimp only [CH];linarith only [hBT,hCBT]
  have hBTC : BT ≤ CH := by dsimp only [CH];linarith only [hBT,hCBT]
  have hCC : CG*BT ≤ CH := by dsimp only [CH];linarith only [hBT,hCBT]
  refine ⟨η,CH,hη,hη1,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s V
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hDegree := hDegree floor hf ε hε hSmall d hd y hy CQ CF CA CM s V
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hr1 := ((radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2).trans (hSmall.trans hη1)
  have hHigh := s.adjoint_higher_taylor_three_jets V hd.1.1 (zero_lt_one.trans_le hK)
    hCQ hCW hr.le hr1 hF0 CD hDegree
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have hAngularHigh := hAngular d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) (frameVectorLinear d.frame y)
    he (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)) hHigh.smooth
    (BT*(d.radius y)^2) (mul_nonneg hBT (sq_nonneg _)) hHigh.bound
  constructor
  · exact hHigh.weaken (mul_le_mul_of_nonneg_right hBTC (sq_nonneg _))
  · intro i j
    refine ⟨mul_nonneg (zero_le_one.trans hCH) (sq_nonneg _),(hAngularHigh i j).1,?_⟩
    intro n hn
    exact ((hAngularHigh i j).2 n hn).trans
      ((show CG*(BT*(d.radius y)^2)=(CG*BT)*(d.radius y)^2 by ring).le.trans
        (mul_le_mul_of_nonneg_right hCC (sq_nonneg _)))
end ShrinkingSpheres
