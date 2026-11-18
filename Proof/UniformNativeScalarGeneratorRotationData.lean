import Proof.NativeScalarGeneratorRotationData
import Proof.UniformNativeScalarAngularOperatorData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def NativeScalarGeneratorRotationData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CK CJ : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (B : ℝ) : Prop :=
  (∀ Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3,
    ∀ R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3,∀ BQ BR : ℝ,
    SmoothFiniteJetBound Q ((y,frameVectorLinear d.frame y),0) 2 BQ →
    (∀ ij,SmoothFiniteJetBound (R ij) ((y,frameVectorLinear d.frame y),0) 2 BR) →
    ∀ a : TaylorGeneratorIndex,
    SmoothFiniteJetBound (A.higherScalarGeneratorFromRotationData ha0 a Q R) ((y,frameVectorLinear d.frame y),0) 2
      (B*(taylorGeneratorWeight (d.radius y) a*(BQ+BR)))) ∧
  ∀ CG : ℝ,∀ G : NativeTaylorGeneratorBounds s h hK CG,
    ∀ Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3,
    ∀ R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3,
    (∀ i j,closedThreeJetHalfBoundaryScalarMultiplierL (R (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q ((y,frameVectorLinear d.frame y),0))) →
    ∀ a : TaylorGeneratorIndex,
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    I1.comp (A.higherScalarGeneratorFromRotationData ha0 a Q R p)=
      (taylorGeneratorScalarCommutator G.scalar F0 ha0 a (Q p)).comp I1 ∧
    (Gh a).comp (closedThreeJetHigherScalarMultiplierL (Q p))-
      (closedThreeJetHalfBoundaryScalarMultiplierL (Q p)).comp (Gh a)=
    I1.comp (A.higherScalarGeneratorFromRotationData ha0 a Q R p)

/-- One physical neighborhood serves all completed three-jet coefficients
    with genuine angular witnesses and any previously selected generators. -/
theorem uniform_native_scalar_generator_rotation_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[nhds z] (fun _ => (1:ℝ)))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    ∃ η CK CJ CH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧ 0 ≤ CJ ∧ 1 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ A : NativeAdjointHalfScalarNeighborhoodData s hd.1.1 (zero_lt_one.trans_le hK) CK CJ,
        NativeScalarGeneratorRotationData A ha0 CH := by
  obtain ⟨η,CK,CJ,CG,hη,hη1,hCK,hCJ,hCG,hShared⟩ := uniform_native_scalar_angular_operator_data
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  let CT := (19+9*Real.sqrt 2)*4*CJ*(1+CG)
  let CD := (19+9*Real.sqrt 2)*‖closedHalfRadialScalarCommutatorL F0 ha0‖
  let CR := ‖closedThreeJetHigherScalarMultiplierL‖
  let CH := 1+CT+CD+CR
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hCT : 0 ≤ CT := by dsimp only [CT];positivity
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCR : 0 ≤ CR := norm_nonneg _
  have hCH : 1 ≤ CH := by dsimp only [CH];linarith
  have hTB : CT ≤ CH := by dsimp only [CH];linarith
  have hDB : CD ≤ CH := by dsimp only [CH];linarith
  have hRB : CR ≤ CH := by dsimp only [CH];linarith
  refine ⟨η,CK,CJ,CH,hη,hη1,hCK,hCJ,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨A,hAngular⟩ := hShared floor hf ε hε hSmall d hd y hy CF CA CM s
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  refine ⟨A,?_,?_⟩
  · intro Q R BQ BR hQ hR a
    exact A.higherScalarGeneratorFromRotationData_jets hCJ ha0 CG hCG0 hAngular CH hTB hDB hRB
      Q R BQ BR hQ hR a
  · intro CG G Q R hR a
    exact ⟨A.higherScalarGeneratorFromRotationData_compatible G hΩ hF0 he ha0 hFlat s.point.flatStrong a Q R hR,
      A.higherScalarGeneratorFromRotationData_graph G hΩ hF0 he ha0 hFlat s.point.flatStrong a Q R hR⟩
end ShrinkingSpheres
