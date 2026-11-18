import Proof.NegativeScalarGeneratorCommutator
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

/-- The positive and negative scalar kernels are compatible because they
represent the SAME actual low scalar commutator. No kernel is replaced. -/
lemma NativeTaylorGeneratorBounds.scalar_kernel_half_negative_compatible
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K C : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K} (A : NativeTaylorGeneratorBounds s h hK C)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (a : TaylorGeneratorIndex) (Q : ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (taylorGeneratorScalarCommutator A.scalar F0 ha0 a Q)=
      (nativeNegativeScalarGeneratorCommutator s ha0 p a Q).comp
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) :=
  (A.generator_low_scalar_commutator hF0 ha0 hFlat s.point.flatStrong a Q).symm.trans
    (A.generator_negative_scalar_commutator hF0 ha0 hFlat s.point.flatStrong a Q)
end ShrinkingSpheres
