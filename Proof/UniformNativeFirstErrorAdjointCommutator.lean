import Proof.NativeAdjointCommutatorData
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
theorem uniform_native_first_error_adjoint_commutator {Y Ω : Set X}
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
      NativeFirstErrorAdjointCommutatorData s CC CH CS := by
  obtain ⟨ηG,CG,hηG,hηG1,hCG,hGenerator⟩ := uniform_native_taylor_generator_bounds hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  obtain ⟨ηD,CK,hηD,hηD1,hCK,hDefect⟩ := uniform_native_adjoint_half_taylor_defect hY hΩ hm
    K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  have ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous _ _ _
      (continuous_pi (fun i => continuous_pi (fun j => (contDiff_coefficientValue 2 (F0 i j)).continuous)))
      continuous_const continuous_const
  have hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1 :=
    fun z hz => hF0 z (unitBall_subset_closedBall_two hz)
  let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let C1 := firstErrorScalarFixedBudget Q0*(27* |M 0| *K+3*K+15*CC)
  let CP := firstErrorAdjointCommonBudget F0 ha0 Q0 CG CK CQ CI CW K (M 0) CC
  let CS := 3*C0^3*C1^2+6*CP^2
  have hCB : 0 ≤ taylorGeneratorFixedBudget F0 ha0 CG := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hC0 : 0 ≤ C0 := add_nonneg hCB (norm_nonneg _)
  have hCS : 0 ≤ CS := by dsimp only [CS];positivity
  refine ⟨min ηG ηD,CS,lt_min hηG hηD,(min_le_left _ _).trans hηG1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨A⟩ := hGenerator floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CF CA CM s
  obtain ⟨KN,hKNJ,hP⟩ := hDefect floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF CA CM s
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hKN := hKNJ.bound 0 (by omega)
  rw [norm_iteratedFDeriv_zero] at hKN
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hε1 := (hSmall.trans (min_le_left _ _)).trans hηG1
  have hr1 := hrε.trans hε1
  exact A.actual_first_error_adjoint_commutator_data hd hK hf hε hε1 hy hr1 hCQ hCI hCW hF0 ha0 hFlat
    Q0 hQ0 hCC (KN p) CK hCK hKN hP
end ShrinkingSpheres
