import Proof.NativeHigherGeneratorCommutator
import Proof.UniformNativeTaylorRotationHigherJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2700
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A single genuine higher family for every Taylor/degree/rotation pair,
with the correct physical commutator graph and common weighted two-jets. -/
def NativeHigherGeneratorCommutatorData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (A : NativeTaylorGeneratorBounds s h hK CG) (B : ℝ) : Prop :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  (∀ a b,SmoothFiniteJetBound (A.higherCommutatorFamily a b) p 2
    (B*(taylorGeneratorWeight (d.radius y) a*taylorGeneratorWeight (d.radius y) b))) ∧
  ∀ a b,
    (taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) b)-
    (taylorGeneratorLow (s.response.adjointHalfTaylor p) b).comp
      (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) a)=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.higherCommutatorFamily a b p)

/-- Closed common higher commutator data, without replacing any already
selected native packet or generator realization. -/
theorem uniform_native_higher_generator_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η CH : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ CG : ℝ,∀ A : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      NativeHigherGeneratorCommutatorData A CH := by
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDegree⟩ := uniform_native_degree_higher_two_jets hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hRotation⟩ := uniform_native_taylor_rotation_higher_jets hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  let η := min ηD ηR
  let CH := 1+CD+CR+4*Real.sqrt 2
  have hCD0 : 0 ≤ CD := zero_le_one.trans hCD
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hS : 0 ≤ 4*Real.sqrt 2 := mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)
  have hCH : 1 ≤ CH := by dsimp only [CH];linarith only [hCD0,hCR0,hS]
  have hCDH : CD ≤ CH := by dsimp only [CH];linarith only [hCR0,hS]
  have hCRH : CR ≤ CH := by dsimp only [CH];linarith only [hCD0,hS]
  have hSH : 4*Real.sqrt 2 ≤ CH := by dsimp only [CH];linarith only [hCD0,hCR0]
  refine ⟨η,CH,lt_min hηD hηR,(min_le_left _ _).trans hηD1,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s CG A
  have hDegree := hDegree floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CQ CF CA CM s A.domain
  have hRotation := hRotation floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF CA CM s A.domain
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  refine ⟨?_,fun a b => A.higherCommutatorFamily_graph hΩ hF0 he a b⟩
  intro a b
  exact A.higherCommutatorFamily_jets CH (zero_le_one.trans hCH) hSH
    (hDegree.2.weaken (mul_le_mul_of_nonneg_right hCDH (sq_nonneg _)))
    (fun i j => (hRotation.2 i j).weaken (mul_le_mul_of_nonneg_right hCRH (sq_nonneg _))) a b

lemma NativeHigherGeneratorCommutatorData.norm_le
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG B : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {A : NativeTaylorGeneratorBounds s h hK CG} (H : NativeHigherGeneratorCommutatorData A B)
    (a b : TaylorGeneratorIndex) :
    ‖A.higherCommutatorFamily a b ((y,frameVectorLinear d.frame y),0)‖ ≤
      B*(taylorGeneratorWeight (d.radius y) a*taylorGeneratorWeight (d.radius y) b) := by
  simpa only [norm_iteratedFDeriv_zero] using (H.1 a b).bound 0 (by norm_num)
end ShrinkingSpheres
