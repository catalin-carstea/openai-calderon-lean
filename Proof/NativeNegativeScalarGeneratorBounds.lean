import Proof.NegativeScalarGeneratorCommutator
import Proof.NativeScalarMultiplierKernelJets
import Proof.NativeTaylorGeneratorNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def nativeNegativeScalarFixedBudget (F0 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CQ CI CW : ℝ) : ℝ :=
  taylorGeneratorFixedBudget F0 ha0
    (2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|))+
    ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖

lemma NativeRelativeHorizontalTaylorData.negative_scalar_generator_weight_bound
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (a : TaylorGeneratorIndex) (Q : ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    ‖nativeNegativeScalarGeneratorCommutator s ha0 p a Q‖ ≤
      nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW*(taylorGeneratorWeight (d.radius y) a*‖Q‖) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let CK := 2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)
  let CB := taylorGeneratorFixedBudget F0 ha0 CK
  let CN := nativeNegativeScalarFixedBudget F0 ha0 CQ CI CW
  obtain ⟨hCB,hCK,hD,hR,hS,hAng⟩ := taylorGeneratorFixedBudget_bounds F0 ha0 CK
  have hCBN : CB ≤ CN := le_add_of_nonneg_right (norm_nonneg _)
  have hNeg : ‖closedNegativeDegreeScalarCommutatorL F0 ha0‖ ≤ CN :=
    le_add_of_nonneg_left (zero_le_one.trans hCB)
  cases a
  · have hh := (s.scalarMultiplierKernel_three_jets hF0 hCQ hCI hCW hr hr1 (fun _ => Q) ‖Q‖
        (SmoothFiniteJetBound.constant Q p 3)).bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    change ‖-(s.coefficients.scalarMultiplierKernel F0 Q p).adjoint‖ ≤ CN*((d.radius y)^2*‖Q‖)
    rw [norm_neg,LinearIsometryEquiv.norm_map]
    exact hh.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCK.trans hCBN) (norm_nonneg Q)) (sq_nonneg _)).trans_eq (by ring))
  · simpa only [nativeNegativeScalarGeneratorCommutator,taylorGeneratorWeight,one_mul] using
      ((closedNegativeDegreeScalarCommutatorL F0 ha0).le_opNorm Q).trans
        (mul_le_mul_of_nonneg_right hNeg (norm_nonneg Q))
  · rename_i i j
    change ‖(closedCoefficientAngularHalfL i j Q).adjoint‖ ≤ CN*(1*‖Q‖)
    rw [LinearIsometryEquiv.norm_map,one_mul]
    exact ((closedCoefficientAngularHalfL i j).le_opNorm Q).trans
      (mul_le_mul_of_nonneg_right ((hAng i j).trans hCBN) (norm_nonneg Q))
end ShrinkingSpheres
