import Proof.NativePotentialScalarPacketFamily
import Proof.NativeScalarBoundedAdjointHigherNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine higher adjoints and compatible low/high mixed commutators for
one weighted generator family. This is the complete data used by a quartic
weak expression, before a change of moving-frame coefficients. -/
structure SphereQuarticGeneratorData {ι : Type*}
    (L : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (w : ι → ℝ) (CA CK : ℝ) where
  adjointHigh : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  commLow : ι → ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  commHigh : ι → ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  adjoint_compatible : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (adjointHigh a)=
    (L a).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  commutator_compatible : ∀ a b,(L a).adjoint.comp (H b)-(L b).comp (adjointHigh a)=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (commHigh a b)
  commutator_balanced : ∀ a b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (commHigh a b)=
    (commLow a b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  adjoint_bound : ∀ a,‖adjointHigh a‖ ≤ CA*w a
  commLow_bound : ∀ a b,‖commLow a b‖ ≤ CK*w a*w b
  commHigh_bound : ∀ a b,‖commHigh a b‖ ≤ CK*w a*w b

/-- The SAME native seven-generator packet family has all49 compatible
mixed-adjoint blocks and uniformly bounded genuine higher adjoints. -/
lemma NativePotentialScalarPacketFamily.quartic_data
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    {G : NativeTaylorGeneratorBounds s h hK CG}
    {EL : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {EH : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)} {CQB CZB CAug CS : ℝ}
    (P : NativePotentialScalarPacketFamily G EL EH CQB CZB CAug)
    (hMixed : NativeScalarPacketMixedAdjointData G CQB CZB CAug CS)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (CKN : ℝ) (hCKN : 0 ≤ CKN) (hKN : ‖KN‖ ≤ CKN*(d.radius y)^2)
    (hP : (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
      s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
        KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))) :
    Nonempty (SphereQuarticGeneratorData (nativePotentialGeneratorLow EL) (nativePotentialGeneratorHigh EH)
      (potentialGeneratorWeight (d.radius y)) (nativeScalarBoundedAdjointHigherBudget F0 ha0 CG CKN CQB CZB) CS) := by
  classical
  have hFlat (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  let Adj (a : PhysicalPotentialGeneratorIndex) := (P.base a).adjointHigherL ha0 KN
  have hAdj (a : PhysicalPotentialGeneratorIndex) :
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Adj a)=
        (nativePotentialGeneratorLow EL a).adjoint.comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    (P.base a).adjoint_balanced_pair hF0 ha0 hFlat KN hP
  let W (a b : PhysicalPotentialGeneratorIndex) := Classical.choice (P.mixed_data hMixed hr a b (Adj a) (hAdj a))
  refine ⟨{ adjointHigh := Adj
            commLow := fun a b => (W a b).low
            commHigh := fun a b => (W a b).high
            adjoint_compatible := hAdj
            commutator_compatible := fun a b => (W a b).graph
            commutator_balanced := fun a b => (W a b).balanced
            adjoint_bound := ?_
            commLow_bound := fun a b => (W a b).low_bound
            commHigh_bound := fun a b => (W a b).high_bound }⟩
  intro a
  exact (P.base a).norm_adjointHigherL_le hF0 ha0 hCQ hCI hCW hr hr1
    (potentialGeneratorWeight_nonneg hr a) KN CKN hCKN hKN
end ShrinkingSpheres
