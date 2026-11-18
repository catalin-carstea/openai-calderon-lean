import Proof.UniformRelativeCenterErrorClosedMultiplier
import Proof.UniformNativeRelativeHorizontalTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The SAME actual center-error multiplier representatives have gained
    joint jets and repeated actual horizontal jets, without frame budgets. -/
theorem uniform_relative_center_error_horizontal_multiplier {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C CH : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ 1 ≤ CH ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,∀ j : I,
      ∃ A : NormalFrameRelativeParameter × X → ℝ,∃ hA : ContDiff ℝ ∞ A,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ p z,z ∉ S → A (p,z)=0,
      ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,frameVectorLinear d.frame y),0) ∈ V ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (p,z)]
          normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j) ∧
        (∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n (commonSupportClosedCoefficientFamily 3 A hA S hS hz)
          ((y,frameVectorLinear d.frame y),0)‖ ≤ C*‖a‖*(d.radius y)^2) ∧
        NormalFrameRelativeHorizontalTaylorBounds d y (commonSupportClosedCoefficientFamily 3 A hA S hS hz) (CH*‖a‖) := by
  obtain ⟨η,C,hη,hη1,hC,hClosed⟩ := uniform_relative_center_error_closed_multiplier_jets hY hΩ
    3 hm K ρ c₀ M Cj hK hρ
  obtain ⟨CH,hCH,hHorizontal⟩ := uniform_normalFrame_horizontal_third_jets hY hΩ hSub (by omega) K M Cj hK
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCH0 : 0 ≤ CH := zero_le_one.trans hCH
  refine ⟨η,C,CH*C,hη,hη1,hC,?_,?_⟩
  · nlinarith only [mul_le_mul hCH hC zero_le_one hCH0]
  intro floor hf ε hε hSmall d hd y hy a j
  obtain ⟨A,hA,S,hS,hz,V,hV,hMem,hRep,hJets⟩ := hClosed floor hf ε hε hSmall d hd y hy a j
  refine ⟨A,hA,S,hS,hz,V,hV,hMem,hRep,hJets,?_⟩
  have hh := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy (ClosedCoefficientJets 3)
    (commonSupportClosedCoefficientFamily 3 A hA S hS hz)
    (contDiff_commonSupportClosedCoefficientFamily 3 A hA S hS hz).contDiffAt
    (C*‖a‖) (d.radius y) (by positivity) hJets
  intro b hb n hn
  exact (hh b hb n hn).trans_eq (by ring)

end ShrinkingSpheres
