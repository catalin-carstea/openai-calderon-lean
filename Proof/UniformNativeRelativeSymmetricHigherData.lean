import Proof.UniformChosenRelativeResponseHigherJets
import Proof.NativeRelativeSymmetricAdjointDomain
import Proof.RelativeNormalCoefficientSymmetryDomain
import Proof.RelativeAngularCoefficientCovariance
import Proof.UniformNativeRelativeHorizontalTaylorData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

structure NativeRelativeSymmetricHigherData {Y Ω : Set X} {d : Data} {y : X}
    {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF0 CA0 CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM)
    (N : ℕ) (CF CA : ℝ) where
  neighborhood : s.response.SymmetricAdjointDomain
  forwardJets : ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n s.response.forwardTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CF*(d.radius y)^2
  adjointJets : ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n s.response.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2

/-- Every already selected genuine physical/native packet has one common
    symmetric inverse domain and every requested higher Taylor jet. Its
    radial response, true adjoint, coframe and center-gradient witnesses are
    preserved. All constants precede the admitted geometry and packet. -/
theorem uniform_native_relative_symmetric_higher_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CI CW : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CF CA : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ CQ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      Nonempty (NativeRelativeSymmetricHigherData s N CF CA) := by
  obtain ⟨ηH,CF,CA,hηH,hηH1,hCF,hCA,hHigher⟩ :=
    uniform_chosen_relative_forward_adjoint_higher_jets hY hΩ N hNm
      K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨ηG,hηG,hGeometry⟩ := uniform_relative_normal_coefficient_symmetric_neighborhood (Y:=Y) hΩ (by omega)
    K ρ c₀ M Cj hK hρ
  refine ⟨min ηH ηG,CF,CA,lt_min hηH hηG,(min_le_left _ _).trans hηH1,hCF,hCA,?_⟩
  intro floor hf ε hε hSmall d hd y hy CQ CF0 CA0 CM s
  obtain ⟨Vg,hVg,hpG,hSubG,hSymG⟩ := hGeometry floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using
      hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  obtain ⟨V⟩ := s.response.exists_native_symmetric_adjoint_domain hΩ hd.1.1 (zero_lt_one.trans_le hK)
    (by norm_num) he F0 CI CW s.point Vg hVg hpG hSymG
  obtain ⟨hForward,hAdjoint⟩ := hHigher floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
    4 CQ s.coefficients s.point s.response
  exact ⟨⟨V,hForward,hAdjoint⟩⟩

end ShrinkingSpheres
