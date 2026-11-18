import Proof.WeakFirstMultiplierDefectEnergy
import Proof.HalfMultiplierTaylorPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

def strongFirstMultiplierDefectL (F0 F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallSobolev 2 :=
  let I0 := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let A1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let K1 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q
  let W1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  fixedStrongH2InclusionL.comp (I0.comp
    (K0.comp W1+K1.comp fixedHarmonicH1LiftL-A1.comp (I0.comp (K0.comp fixedHarmonicH1LiftL))))

/-- The first gained boundary variation is the trace of the actual
linearized strong multiplier defect. -/
theorem halfMultiplierFirstVariation_eq_trace (F0 F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    halfMultiplierFirstVariationL F0 F1 ha1 Q = fixedHalfOutwardTraceL.comp (strongFirstMultiplierDefectL F0 F1 ha1 Q) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [halfMultiplierFirstVariationL,strongFirstMultiplierDefectL,ContinuousLinearMap.comp_apply,
    add_apply,sub_apply,neg_apply,map_sub,map_add,map_neg]
  simp only [sub_eq_add_neg]

/-- Linearized strong and weak multiplication defects are the same
zero-boundary solution, by the genuine flat-coefficient energy uniqueness. -/
theorem firstOrder_strongFirstMultiplierDefect (F0 F1 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc0 : IsCoercive (TauCeti.PDE.energyFormH1L0 ha0))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (1/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (strongFirstMultiplierDefectL F0 F1 ha1 Q f) = weakFirstMultiplierDefectL F1 ha1 Q f := by
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  let A1 := strongDirichletOperator fixedSobolevCalculus 0 F1
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let K1 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q
  let W1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  let U0 := A0.inverse (K0 (fixedHarmonicH1LiftL f))
  let G : BallSobolev 0 := K0 (W1 f)+K1 (fixedHarmonicH1LiftL f)-A1 U0
  let U1 := A0.inverse G
  let V1 : BallH1Zero := ⟨weakFirstMultiplierDefectL F1 ha1 Q f,weakFirstMultiplierDefect_mem_zero F1 ha1 Q f⟩
  have hW0 : nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner = fixedHarmonicH1LiftL :=
    (nativeWeakHalfLift_congr_unitBall ha0 (flatCoefficientBound 1) (by intro z hz;simpa using hFlat z hz)).trans
      (nativeWeakHalfLift_flat_eq 1 (flatCoefficientBound 1))
  have hU0 : (U0:BallSobolev 2) = strongPoissonMultiplierDefectL F0 ha0 Q f := by
    change (U0:BallSobolev 2) = fixedStrongH2InclusionL
      (A0.inverse (K0 (nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner f)))
    rw [hW0]
    rfl
  have hFirst0 : TauCeti.Wkp.firstOrder 1 (U0:BallSobolev 2) = weakPoissonMultiplierDefectL F0 ha0 Q f :=
    (congrArg (TauCeti.Wkp.firstOrder 1) hU0).trans (firstOrder_strongPoissonMultiplierDefect F0 ha0 hc0 hInv0 Q f)
  have hV : V1 = TauCeti.PDE.weakSolutionDirichlet ha0 hc0 G := by
    apply TauCeti.PDE.eq_weakSolutionDirichlet ha0 hc0
    intro v
    have hE := weakFirstMultiplierDefect_energy F0 F1 ha0 ha1 hFlat Q f v
    have hFlux : ⟪A1 U0,TauCeti.W1p.value (v:BallH1)⟫_ℝ =
        TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F1) 0 0
          (TauCeti.Wkp.firstOrder 1 (U0:BallSobolev 2)) (v:BallH1) := by
      have hRaw : ⟪A1 U0,TauCeti.W1p.value (v:BallH1)⟫_ℝ =
          TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F1) 0 0
            (strongDirichletProjectionL 0 U0:BallH1) (v:BallH1) := by
        simpa only [Nat.zero_add,TauCeti.PDE.dirichletForcing_apply,TauCeti.Wkp.value_zero] using
          strongCoefficientOperator_energy fixedSobolevCalculus 0 F1 U0 v
      exact hRaw.trans (congrArg (fun w : BallH1 =>
        TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F1) 0 0 w (v:BallH1))
        (strongDirichletProjectionL_apply 0 U0))
    rw [hFirst0] at hFlux
    have hG : ⟪G,TauCeti.W1p.value (v:BallH1)⟫_ℝ =
        ⟪K0 (W1 f),TauCeti.W1p.value (v:BallH1)⟫_ℝ+
        ⟪K1 (fixedHarmonicH1LiftL f),TauCeti.W1p.value (v:BallH1)⟫_ℝ-
        TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F1) 0 0
          (weakPoissonMultiplierDefectL F0 ha0 Q f) (v:BallH1) := by
      dsimp only [G]
      rw [inner_sub_left,inner_add_left,hFlux]
    simpa only [Pi.zero_def,V1,TauCeti.PDE.dirichletForcing_apply] using hE.trans hG.symm
  have hU : strongDirichletProjectionL 0 U1 = TauCeti.PDE.weakSolutionDirichlet ha0 hc0 G := by
    apply TauCeti.PDE.eq_weakSolutionDirichlet ha0 hc0
    intro v
    have hAU : A0 U1 = G := hInv0.self_apply_inverse G
    have hE := (strongCoefficientOperator_energy fixedSobolevCalculus 0 F0 U1 v).symm
    rw [hAU] at hE
    simpa only [Nat.zero_add,Pi.zero_def,TauCeti.Wkp.value_zero] using hE
  have hSame := congrArg (fun w : BallH1Zero => (w:BallH1)) (hU.trans hV.symm)
  have hU1 : strongFirstMultiplierDefectL F0 F1 ha1 Q f = (U1:BallSobolev 2) := rfl
  rw [hU1]
  exact hSame

end ShrinkingSpheres
