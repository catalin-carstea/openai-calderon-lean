import Proof.FullFirstAdjointCommutatorData
import Proof.UniformFirstDerivativeScalarData
import Proof.HalfTaylorAdjointDefect
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- Closed common mixed adjoint commutator bound for the full actual
first-base coefficient. Constants precede arbitrary admitted profiles and
ANY selected physical principal data. No frame derivative budget is used. -/
theorem uniform_full_first_derivative_adjoint_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ CDF CDT : ℝ,
      ∀ D : PhysicalPrincipalData Y d CDF CDT,∀ y ∈ Y,
      FullFirstAdjointCommutatorData D y (CS*(ε/beta d.γ d.radius y)^2) := by
  obtain ⟨ηS,CF,CA,CM,CQ,CI,CW,CG,CQB,CZB,F0,Q0,
    hηS,hηS1,hCQ,hCI,hCW,hCG,hCQB,hCZB,hF0,hQ0,hScalar⟩ :=
    uniform_full_first_derivative_scalar_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηD,CK,hηD,hηD1,hCK,hDefect⟩ := uniform_native_adjoint_half_taylor_defect hY hΩ hm
    K ρ c₀ M Cj hK hρ CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0
  have ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens) :=
    memLp_nativeEnergyIntegrand_of_continuous _ _ _
      (continuous_pi (fun i => continuous_pi (fun j => (contDiff_coefficientValue 2 (F0 i j)).continuous)))
      continuous_const continuous_const
  have hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1 :=
    fun z hz => hF0 z (unitBall_subset_closedBall_two hz)
  let C0 := taylorGeneratorFixedBudget F0 ha0 CG+‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  let CP := fullFirstAdjointCommonBudget F0 ha0 CG CK CQ CI CW CQB CZB
  let CS := 3*C0^3*CQB^2+6*CP^2
  have hCB : 0 ≤ taylorGeneratorFixedBudget F0 ha0 CG := zero_le_one.trans (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hC0 : 0 ≤ C0 := add_nonneg hCB (norm_nonneg _)
  have hCS : 0 ≤ CS := by dsimp only [CS];positivity
  refine ⟨min ηS ηD,CS,lt_min hηS hηD,(min_le_left _ _).trans hηS1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd CDF CDT D y hy
  have hεS := hSmall.trans (min_le_left _ _)
  have hεD := hSmall.trans (min_le_right _ _)
  obtain ⟨s,T,hB⟩ := hScalar floor hf ε hε hεS d hd y hy
  obtain ⟨B⟩ := hB CDF CDT D
  obtain ⟨KN,hKNJ,hP⟩ := hDefect floor hf ε hε hεD d hd y hy CF CA CM s
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hKN := hKNJ.bound 0 (by omega)
  rw [norm_iteratedFDeriv_zero] at hKN
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hε1 := hεS.trans hηS1
  have hr1 := ((radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2).trans hε1
  have hβ : 0 ≤ beta d.γ d.radius y := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  exact B.adjoint_commutator_data hCQB (div_nonneg hε hβ) hF0 he ha0 hFlat
    (zero_le_one.trans hCQ) hCI hCW hr.le hr1 (KN p) CK hCK hKN hP
end ShrinkingSpheres
