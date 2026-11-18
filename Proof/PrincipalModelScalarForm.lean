import Proof.FlatRaisingRightScalarForm
import Proof.DegreeScalarCoefficients
import Proof.TaylorScalarCoefficientCalculus
import Proof.PrincipalModelFirstDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def degreeRaisingScalarCoefficients (Q0 : SmoothCoefficientJets 2) (c b : I → ℝ) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 :=
  (∑ i : I,c i • degreeScalarCoefficients Q0)+(2:ℝ) • (∑ i : I,b i • flatRaisingScalarCoefficients Q0 i)

def principalModelScalarCoefficients (Q0 : SmoothCoefficientJets 2) (d : Data) (y : X) (j : I) :
    TaylorGeneratorIndex → ClosedCoefficientJets 3 :=
  degreeRaisingScalarCoefficients Q0
    (fun i => (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
      frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*scaledFrameLogRadius d.radius d.frame i y)
    (fun i => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0))

lemma degreeRaisingScalarCoefficients_form {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : TaylorGeneratorIndex → E →L[ℝ] F) (M : ClosedCoefficientJets 3 →L[ℝ] (E →L[ℝ] E))
    (Q0 : SmoothCoefficientJets 2) (c b : I → ℝ) (D : E →L[ℝ] F) (R : I → E →L[ℝ] F)
    (hD : rightScalarCombinationL G M (degreeScalarCoefficients Q0)=D)
    (hR : ∀ i,rightScalarCombinationL G M (flatRaisingScalarCoefficients Q0 i)=R i) :
    rightScalarCombinationL G M (degreeRaisingScalarCoefficients Q0 c b)=
      (∑ i : I,c i • D)+(2:ℝ) • (∑ i : I,b i • R i) := by
  simp only [degreeRaisingScalarCoefficients,map_add,map_sum,map_smul,hD,hR]

def principalModelFirstDerivativeHigherL (d : Data) (y : X) (j : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (∑ i : I,((frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*scaledFrameLogRadius d.radius d.frame i y) •
      sphereSobolevShiftedDegreeL (3/2:ℝ))+
    (2:ℝ) • (∑ i : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)) •
      flatThreeHalfRaisingL i)

lemma NativeTaylorGeneratorBounds.principal_model_scalar_endpoints
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK CG)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (j : I) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (∑ a,(taylorGeneratorLow (s.response.adjointHalfTaylor p) a).comp
      (closedThreeJetHalfBoundaryScalarMultiplierL (principalModelScalarCoefficients Q0 d y j a)))=
        principalModelFirstDerivativeHalfL d y j ∧
    (∑ a,(taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p) a).comp
      (closedThreeJetHigherScalarMultiplierL (principalModelScalarCoefficients Q0 d y j a)))=
        principalModelFirstDerivativeHigherL d y j := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let c : I → ℝ := fun i => (frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j+
    frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) j i)*scaledFrameLogRadius d.radius d.frame i y
  let b : I → ℝ := fun i => frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j-(if i=j then 1 else 0)
  constructor
  · have hD := degree_scalar_coefficients_form (taylorGeneratorLow (s.response.adjointHalfTaylor p))
      closedThreeJetHalfBoundaryScalarMultiplierL Q0 (closedUnitCoefficient_half Q0 hQ0)
    have hR (i : I) := (A.flat_raising_scalar_endpoints hF0 Q0 hQ0 i).1
    have hh := degreeRaisingScalarCoefficients_form (taylorGeneratorLow (s.response.adjointHalfTaylor p))
      closedThreeJetHalfBoundaryScalarMultiplierL Q0 c b _ flatHalfRaisingL hD
      (fun i => by simpa only [rightScalarCombinationL_apply] using hR i)
    simpa only [rightScalarCombinationL_apply,principalModelScalarCoefficients,principalModelFirstDerivativeHalfL,c,b,taylorGeneratorLow] using hh
  · have hD := degree_scalar_coefficients_form (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p))
      closedThreeJetHigherScalarMultiplierL Q0 (closedUnitCoefficient_higher Q0 hQ0)
    have hR (i : I) := (A.flat_raising_scalar_endpoints hF0 Q0 hQ0 i).2
    have hh := degreeRaisingScalarCoefficients_form (taylorGeneratorHigh (A.domain.adjointHigherTaylor h hK (by norm_num) p))
      closedThreeJetHigherScalarMultiplierL Q0 c b _ flatThreeHalfRaisingL hD
      (fun i => by simpa only [rightScalarCombinationL_apply] using hR i)
    simpa only [rightScalarCombinationL_apply,principalModelScalarCoefficients,principalModelFirstDerivativeHigherL,c,b,taylorGeneratorHigh] using hh
end ShrinkingSpheres
