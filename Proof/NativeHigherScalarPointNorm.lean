import Proof.UniformNativeScalarGeneratorRotationData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ B : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

/-- Pointwise higher scalar norms need only the coefficient and the same
    explicit angular coefficients, via constant-family specialization. -/
lemma higherScalarGeneratorFromRotationData_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 B)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (R : I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3) (a : TaylorGeneratorIndex) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    ‖A.higherScalarGeneratorFromRotationData ha0 a Q R p‖ ≤
      B*(taylorGeneratorWeight (d.radius y) a*(‖Q p‖+∑ ij : I × I,‖R ij p‖)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let BR := ∑ ij : I × I,‖R ij p‖
  have hR (ij : I × I) : SmoothFiniteJetBound (fun _ : NormalFrameRelativeParameter => R ij p) p 2 BR :=
    (SmoothFiniteJetBound.constant (R ij p) p 2).weaken
      (Finset.single_le_sum (fun k _ => norm_nonneg (R k p)) (Finset.mem_univ ij))
  have hh := H.1 (fun _ => Q p) (fun ij _ => R ij p) ‖Q p‖ BR
    (SmoothFiniteJetBound.constant (Q p) p 2) hR a
  have hn := hh.bound 0 (by norm_num)
  rw [norm_iteratedFDeriv_zero] at hn
  have hEq : A.higherScalarGeneratorFromRotationData ha0 a (fun _ => Q p) (fun ij _ => R ij p) p=
      A.higherScalarGeneratorFromRotationData ha0 a Q R p := by
    cases a <;> rfl
  rw [hEq] at hn
  exact hn
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
