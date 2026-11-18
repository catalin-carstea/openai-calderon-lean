import Proof.UniformNativeDegreeHigherJetBounds
import Proof.NativeTaylorGeneratorSystem
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- SAME selected Taylor/degree generator commutator with a genuine
higher endpoint and both higher degree-family two-jet bounds. -/
def NativeTaylorDegreeHigherData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (A : NativeTaylorGeneratorBounds s h hK CG) (B : ℝ) : Prop :=
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  A.domain.HigherDegreeJetBound h hK (by norm_num) p 2 (B*(d.radius y)^2) ∧
  (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
    (A.domain.adjointDegreeHigherFamily h hK (by norm_num) p)=
    (A.domain.degreeFamily h hK (by norm_num) p).adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
  (s.response.adjointHalfTaylor p).comp (sphereSobolevShiftedDegreeL (3/2:ℝ))-
    (sphereSobolevShiftedDegreeL (1/2:ℝ)).comp (A.domain.adjointHigherTaylor h hK (by norm_num) p)=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.domain.adjointDegreeHigherFamily h hK (by norm_num) p)

lemma NativeTaylorGeneratorBounds.degree_higher_data
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (A : NativeTaylorGeneratorBounds s h hK CG) (hΩ : IsOpen Ω)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (B : ℝ) (hJets : A.domain.HigherDegreeJetBound h hK (by norm_num)
      ((y,frameVectorLinear d.frame y),0) 2 (B*(d.radius y)^2)) :
    NativeTaylorDegreeHigherData A B := by
  have hHigh := A.domain.adjointDegreeHigherFamily_compatible hΩ h hK (by norm_num) _ A.domain.pointMem
  refine ⟨hJets,hHigh,?_⟩
  have hGen := A.generator_commutator_graph hF0 he .taylor .degree
  exact hGen.trans hHigh.symm

/-- Closed common higher Taylor/degree commutator data for ANY native
packet and ANY already selected generator realization. -/
theorem uniform_native_taylor_degree_higher_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CI CW : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η CH : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CQ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ CG : ℝ,∀ A : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      NativeTaylorDegreeHigherData A CH := by
  obtain ⟨η,CH,hη,hη1,hCH,hHigher⟩ := uniform_native_degree_higher_two_jets hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  refine ⟨η,CH,hη,hη1,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CQ CF CA CM s CG A
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  exact A.degree_higher_data hΩ hF0 he CH (hHigher floor hf ε hε hSmall d hd y hy CQ CF CA CM s A.domain)
end ShrinkingSpheres
