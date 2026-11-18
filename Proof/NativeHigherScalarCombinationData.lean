import Proof.NativeHigherScalarCombinationGraph
import Proof.UniformNativeHigherGeneratorCommutator
import Proof.NativeHigherScalarPointNorm
import Proof.NativeHigherGeneratorNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS BG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def scalarCombinationHigherFamily (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q R : TaylorGeneratorIndex → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (AQ AR : TaylorGeneratorIndex → I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  G.higherScalarCombinationCommutator (fun a => Q a p) (fun b => R b p)
    (fun b a => A.higherScalarGeneratorFromRotationData ha0 b (Q a) (AQ a) p)
    (fun a b => A.higherScalarGeneratorFromRotationData ha0 a (R b) (AR b) p) p

lemma scalarCombinationHigherFamily_graph
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hΩ : IsOpen Ω) (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q R : TaylorGeneratorIndex → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (AQ AR : TaylorGeneratorIndex → I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hAQ : ∀ a i j,closedThreeJetHalfBoundaryScalarMultiplierL (AQ a (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (Q a ((y,frameVectorLinear d.frame y),0)))
    (hAR : ∀ b i j,closedThreeJetHalfBoundaryScalarMultiplierL (AR b (i,j) ((y,frameVectorLinear d.frame y),0))=
      closedCoefficientAngularHalfL i j (R b ((y,frameVectorLinear d.frame y),0))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    (∑ a,(Gl a).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Q a p))).comp
      (∑ b,(Gh b).comp (closedThreeJetHigherScalarMultiplierL (R b p)))-
    (∑ b,(Gl b).comp (closedThreeJetHalfBoundaryScalarMultiplierL (R b p))).comp
      (∑ a,(Gh a).comp (closedThreeJetHigherScalarMultiplierL (Q a p)))=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.scalarCombinationHigherFamily G ha0 Q R AQ AR p) :=
  G.higherScalarCombinationCommutator_graph hΩ hF0 he ha0 hFlat hInv0 _ _ _ _
    (fun b a => (H.2 CG G (Q a) (AQ a) (hAQ a) b).1)
    (fun a b => (H.2 CG G (R b) (AR b) (hAR b) a).1)

/-- Higher finite commutator norms expose the actual coefficient/angular
    weighted sums; the exact selected generators and scalar witnesses agree. -/
lemma scalarCombinationHigherFamily_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS) (HG : NativeHigherGeneratorCommutatorData G BG)
    (Q R : TaylorGeneratorIndex → NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (AQ AR : TaylorGeneratorIndex → I × I → NormalFrameRelativeParameter → ClosedCoefficientJets 3) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    ‖A.scalarCombinationHigherFamily G ha0 Q R AQ AR p‖ ≤
      3*C^3*(∑ a,taylorGeneratorWeight (d.radius y) a*(‖Q a p‖+∑ ij : I × I,‖AQ a ij p‖))*
        (∑ b,taylorGeneratorWeight (d.radius y) b*(‖R b p‖+∑ ij : I × I,‖AR b ij p‖)) := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let CB := taylorGeneratorFixedBudget F0 ha0 CG
  let C := CB+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let w := taylorGeneratorWeight (d.radius y)
  let q := fun a => ‖Q a p‖+∑ ij : I × I,‖AQ a ij p‖
  let r := fun b => ‖R b p‖+∑ ij : I × I,‖AR b ij p‖
  let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
  have hCB : 1 ≤ CB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hGC : CB+2 ≤ C := by dsimp only [C];linarith [abs_nonneg BG,abs_nonneg BS,norm_nonneg closedThreeJetHigherScalarMultiplierL]
  have hBGC : BG ≤ C := by dsimp only [C];linarith [le_abs_self BG,abs_nonneg BS,norm_nonneg closedThreeJetHigherScalarMultiplierL]
  have hBSC : BS ≤ C := by dsimp only [C];linarith [le_abs_self BS,abs_nonneg BG,norm_nonneg closedThreeJetHigherScalarMultiplierL]
  have hMC : ‖closedThreeJetHigherScalarMultiplierL‖ ≤ C := by dsimp only [C];linarith [abs_nonneg BS,abs_nonneg BG]
  have hw (a : TaylorGeneratorIndex) : 0 ≤ w a := by cases a <;> simp only [w,taylorGeneratorWeight] <;> positivity
  have hq (a : TaylorGeneratorIndex) : 0 ≤ q a := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hr (a : TaylorGeneratorIndex) : 0 ≤ r a := add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hQn (a : TaylorGeneratorIndex) : ‖Q a p‖ ≤ q a := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hRn (b : TaylorGeneratorIndex) : ‖R b p‖ ≤ r b := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  apply norm_rightMultiplierCombinationCommutatorL_of_weights Gh (fun a b => G.higherCommutatorFamily a b p)
    (fun a => closedThreeJetHigherScalarMultiplierL (Q a p))
    (fun b => closedThreeJetHigherScalarMultiplierL (R b p))
    (fun b a => A.higherScalarGeneratorFromRotationData ha0 b (Q a) (AQ a) p)
    (fun a b => A.higherScalarGeneratorFromRotationData ha0 a (R b) (AR b) p) C w q r hC hw hq hr
  · intro a
    exact (G.high_generator_weight_bounds ha0 a).trans (mul_le_mul_of_nonneg_right hGC (hw a))
  · intro a b
    exact (HG.norm_le a b).trans (mul_le_mul_of_nonneg_right hBGC (mul_nonneg (hw a) (hw b)))
  · intro a
    exact (closedThreeJetHigherScalarMultiplierL.le_opNorm (Q a p)).trans
      (mul_le_mul hMC (hQn a) (norm_nonneg _) hC)
  · intro b
    exact (closedThreeJetHigherScalarMultiplierL.le_opNorm (R b p)).trans
      (mul_le_mul hMC (hRn b) (norm_nonneg _) hC)
  · intro b a
    exact (A.higherScalarGeneratorFromRotationData_norm_le ha0 HS (Q a) (AQ a) b).trans
      (mul_le_mul_of_nonneg_right hBSC (mul_nonneg (hw b) (hq a)))
  · intro a b
    exact (A.higherScalarGeneratorFromRotationData_norm_le ha0 HS (R b) (AR b) a).trans
      (mul_le_mul_of_nonneg_right hBSC (mul_nonneg (hw a) (hr b)))
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
