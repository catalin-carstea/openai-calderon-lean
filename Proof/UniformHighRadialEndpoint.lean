import Proof.StrongPoissonPerturbation
import Proof.UniformStrongPerturbationData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The actual normalized coefficient has a uniformly small completed radial
    endpoint from boundary H3/2 to boundary H1/2. The same representative carries
    its genuine coefficient germ and the invertible Dirichlet operator. -/
theorem uniform_actual_high_radial_endpoint {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CH : ℝ,0 < η ∧ 0 ≤ CH ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ F : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
          coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => principalCoefficient
            (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖fixedHalfOutwardTraceL.comp (strongPoissonL F)-fixedHalfOutwardTraceL.comp fixedHarmonicLiftL‖ ≤
          CH*d.radius y := by
  obtain ⟨η,C,Q,F0,hη,hC,hQ,hF0,hData⟩ := uniform_actual_strong_flat_data
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  let B := fullC1OperatorBudget fixedSobolevCalculus
  let CH := ‖fixedHalfOutwardTraceL‖*(C*B*Q*‖fixedHarmonicLiftL‖)
  have hB : 0 ≤ B := fullC1OperatorBudget_nonneg _
  have hCH : 0 ≤ CH := mul_nonneg (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg hC hB) hQ) (norm_nonneg _))
  refine ⟨η,CH,hη,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨F,c,hc,hRep,hInv,hNorm,hValue,hDerivative⟩ := hData floor hf ε hε hSmall d hd y hy
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := norm_halfRadialPoisson_sub_flat_le F F0 c C (Q*d.radius y) hC (mul_nonneg hQ hr.le)
    (fun x hx => hF0 x (unitBall_subset_closedBall_two hx)) hNorm hValue hDerivative
  exact ⟨F,hRep,hInv,hb.trans_eq (by dsimp only [CH,B];ring)⟩

end ShrinkingSpheres
