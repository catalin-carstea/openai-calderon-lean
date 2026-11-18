import Proof.PhysicalFirstAdjointHigherBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- One smooth genuine higher adjoint of every full actual first-base
coefficient, with the original epsilon/beta gain and constants before tests. -/
theorem uniform_physical_first_derivative_smooth_adjoint_higher {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ H : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∀ j : I,ContDiffOn ℝ ∞ (H j) Y ∧ ∀ x ∈ Y,
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H j x)=
          (P.firstDerivativeHalfL x j).adjoint.comp
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖H j x‖ ≤ CB*ε/beta d.γ d.radius x := by
  have hRProduce := uniform_flat_raising_constant_adjoint_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hRData⟩ := hRProduce
  have hEProduce := uniform_physical_frame_first_error_smooth_adjoint_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηE,CA,hηE,hηE1,hCA,hEData⟩ := hEProduce
  let CB := 108*(K+1)*K^2+54*K^2*CR+
    54*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+CA)
  have hF := firstCorrectionGradeBound_nonneg (-(1/2:ℝ)) K (M ⟨1,by omega⟩)
  have hCB : 0 ≤ CB := by dsimp only [CB];positivity
  refine ⟨min ηR ηE,CB,lt_min hηR hηE,(min_le_left _ _).trans hηR1,hCB,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨AR,hAR⟩ := hRData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  obtain ⟨AE,hAE⟩ := hEData floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CT P
  refine ⟨fun j x => P.firstDerivativeAdjointHigherFamily AR AE x j,?_⟩
  intro j
  refine ⟨P.firstDerivativeAdjointHigherFamily_smooth hY hΩ hd (zero_lt_one.trans_le hK)
    AR AE (fun i => (hAE i).1) j,?_⟩
  intro x hx
  refine ⟨P.firstDerivativeAdjointHigherFamily_balanced AR AE x
    (fun i => (hAR x hx i).1) (fun i => ((hAE i).2 x hx).1) j,?_⟩
  exact P.norm_firstDerivativeAdjointHigherFamily_small hΩ (by omega) hd hK hf hε
    (hSmall.trans ((min_le_left _ _).trans hηR1)) AR AE hCR hCA hx
    (fun i => (hAR x hx i).2) (fun i => ((hAE i).2 x hx).2) j
end ShrinkingSpheres
