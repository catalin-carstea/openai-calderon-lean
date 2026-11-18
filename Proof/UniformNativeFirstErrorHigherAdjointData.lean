import Proof.UniformNativeFirstErrorHigherAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Closed common uniform mixed adjoint commutator producer. It supplies
genuine higher adjoint endpoints and then works for ANY already selected
compatible endpoints. All constants precede admitted profiles and frames. -/
theorem uniform_native_first_error_higher_adjoint_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (CC CH : ℝ) (hCC : 0 ≤ CC) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      NativeFirstErrorHigherAdjointCommutatorData s CC CH CS := by
  obtain ⟨ηG,CG,hηG,hηG1,_hCG,hGenerator⟩ := uniform_native_taylor_generator_bounds hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  have ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous _ _ _
      (continuous_pi (fun i => continuous_pi (fun j => (contDiff_coefficientValue 2 (F0 i j)).continuous)))
      continuous_const continuous_const
  obtain ⟨ηH,CS,hηH,_hηH1,hCS,hHigher⟩ := uniform_native_first_error_higher_adjoint_commutator
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW
      F0 hF0 Q0 hQ0 ha0 CC CH hCC CG
  refine ⟨min ηG ηH,CS,lt_min hηG hηH,(min_le_left _ _).trans hηG1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨G⟩ := hGenerator floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CF CA CM s
  exact hHigher floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF CA CM s G
end ShrinkingSpheres
