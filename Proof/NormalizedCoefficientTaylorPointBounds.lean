import Proof.NormalizedStrongTaylorPointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local irreducible] strongDirichletOperator fullCoefficientOperatorL strongCoefficientOperatorL

/-- The existing normalized strong point theorem exposes its coefficient C1
    Taylor data without carrying unused strong inverse propositions downstream. -/
theorem uniform_normalized_coefficient_taylor_point_bounds {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η P Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ P ∧ 0 ≤ Q ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ F F1 : SmoothCoefficientMatrix 2,
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
        (fun w => normalizedFirstNormalCoefficient d y w i j)) →
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
        (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) →
      (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) z| ≤ P) ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ P) ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-F0-d.radius y • F1) i j) z| ≤ Q*(d.radius y)^2) ∧
      (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-F0-d.radius y • F1) i j)) z‖ ≤ Q*(d.radius y)^2) := by
  obtain ⟨η,CI,P,Q,F0,hη,hCI,hP,hQ,hF0,hPoint⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,P,Q,F0,hη,hP,hQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  obtain ⟨hInv,hInvNorm,hInv0,hInv0Norm,hVal1,hDer1,hValR,hDerR⟩ :=
    hPoint floor hf ε hε hSmall d hd y hy F F1 hRep hRep1
  exact ⟨hVal1,hDer1,hValR,hDerR⟩

end ShrinkingSpheres
