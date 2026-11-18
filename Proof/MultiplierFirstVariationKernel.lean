import Proof.HalfMultiplierTaylorPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Scalar distribution for the actual first inverse/product variation,
proved with abstract normed spaces so no native Sobolev types are unfolded. -/
lemma operator_first_variation_smul
    {H U V W Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I : V →L[ℝ] W) (A : W →L[ℝ] V)
    (K0 K1 : U →L[ℝ] V) (P : H →L[ℝ] U) (c : ℝ) :
    T.comp (I.comp (K0.comp (c • P)+(c • K1).comp H0)+
      (-(I.comp ((c • A).comp I))).comp (K0.comp H0)) =
      c • T.comp (I.comp (K0.comp P+K1.comp H0)+
        (-(I.comp (A.comp I))).comp (K0.comp H0)) := by
  simp only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_neg,ContinuousLinearMap.neg_comp,smul_add,smul_neg]

lemma negative_composition_four_smul
    {H U V W Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (J : W →L[ℝ] Z) (I : V →L[ℝ] W) (T : U →L[ℝ] V) (L : H →L[ℝ] U) (c : ℝ) :
    -(J.comp (I.comp ((c • T).comp L))) = c • (-(J.comp (I.comp (T.comp L)))) := by
  simp only [ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_neg]

/-- The typed first variation formula, with each actual factor exposed once.
This is the native formula, including the genuine inverse variation. -/
def multiplierFirstVariationKernel
    (I0 : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (A1 : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0)
    (K0 K1 : BallH1 →L[ℝ] BallSobolev 0)
    (P1 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL).comp
    (I0.comp (K0.comp P1+K1.comp fixedHarmonicH1LiftL)+
      (-(I0.comp (A1.comp I0))).comp (K0.comp fixedHarmonicH1LiftL))

lemma halfMultiplierFirstVariation_kernel (F0 F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) :
    halfMultiplierFirstVariationL F0 F1 ha1 Q = multiplierFirstVariationKernel
      (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 F1)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q)
      (weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1) := rfl

lemma multiplierFirstVariationKernel_congr
    {I J : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0}
    {A B : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0}
    {K0 K1 L0 L1 : BallH1 →L[ℝ] BallSobolev 0}
    {P Q : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1}
    (hI : I=J) (hA : A=B) (hK0 : K0=L0) (hK1 : K1=L1) (hP : P=Q) :
    multiplierFirstVariationKernel I A K0 K1 P = multiplierFirstVariationKernel J B L0 L1 Q := by
  rw [hI,hA,hK0,hK1,hP]

lemma multiplierFirstVariationKernel_smul
    (I : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (A : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0)
    (K0 K1 : BallH1 →L[ℝ] BallSobolev 0)
    (P : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1) (c : ℝ) :
    multiplierFirstVariationKernel I (c • A) K0 (c • K1) (c • P) =
      c • multiplierFirstVariationKernel I A K0 K1 P := by
  exact operator_first_variation_smul (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL)
    fixedHarmonicH1LiftL I A K0 K1 P c

end ShrinkingSpheres
