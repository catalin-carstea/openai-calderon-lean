import Proof.UniformFirstDerivativeScalarData
import Proof.NativeScalarBoundedEndpointData
import Proof.NativeFirstErrorAdjointEndpoints
import Proof.NativeTaylorScalarAdjointNormalForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeScalarBoundedEndpointData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
  {T : NativeTaylorGeneratorBounds s h hK CG} {CQB CZB scale : ℝ}
  {L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
  {H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)}

/-- Scalar and bounded parts give the SAME physical low/high square. -/
lemma balanced_pair (B : NativeScalarBoundedEndpointData T L H CQB CZB scale)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hGen := T.scalar_combination_balanced_pair hF0 B.coefficient
  have hZ : I0.comp (B.boundedHalf.comp I1)=(B.boundedNegative.comp I0).comp I1 := by
    exact (ContinuousLinearMap.comp_assoc _ _ _).symm.trans
      (congrArg (fun F => F.comp I1) B.bounded_pair)
  let Lo := rightScalarCombinationL (taylorGeneratorLow (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)))
    closedThreeJetHalfBoundaryScalarMultiplierL B.coefficient
  let Hi := rightScalarCombinationL
    (taylorGeneratorHigh (T.domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)))
    closedThreeJetHigherScalarMultiplierL B.coefficient
  have hGen' : I0.comp Hi=Lo.comp I1 := by
    simpa only [Hi,Lo,rightScalarCombinationL_apply] using hGen
  calc
    I0.comp H=I0.comp (Hi+B.boundedHalf.comp I1) := congrArg (fun F => I0.comp F) B.high_form
    _=I0.comp Hi+I0.comp (B.boundedHalf.comp I1) := ContinuousLinearMap.comp_add _ _ _
    _=Lo.comp I1+(B.boundedNegative.comp I0).comp I1 := congrArg₂
      (fun A B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A+B) hGen' hZ
    _=(Lo+B.boundedNegative.comp I0).comp I1 := (ContinuousLinearMap.add_comp _ _ _).symm
    _=L.comp I1 := congrArg (fun F => F.comp I1) B.low_form.symm
end NativeScalarBoundedEndpointData

/-- Genuine full first-base endpoint squares for ANY already selected
    physical principal packet, uniformly before all admitted data. -/
theorem uniform_full_first_derivative_balanced_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ CF CT : ℝ,∀ D : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,∀ j : I,
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (D.firstDerivativeHigherL y j)=
          (D.firstDerivativeHalfL y j).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  obtain ⟨η,CF,CA,CM,CQ,CI,CW,CG,CQB,CZB,F0,Q0,hη,hη1,_hCQ,_hCI,_hCW,_hCG,_hCQB,_hCZB,hF0,_hQ0,hData⟩ :=
    uniform_full_first_derivative_scalar_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,hη1,?_⟩
  intro floor hf ε hε hSmall d hd CDF CDT D y hy j
  obtain ⟨s,T,hPoint⟩ := hData floor hf ε hε hSmall d hd y hy
  obtain ⟨B⟩ := hPoint CDF CDT D
  exact (B.endpointData j).balanced_pair hF0
end ShrinkingSpheres
