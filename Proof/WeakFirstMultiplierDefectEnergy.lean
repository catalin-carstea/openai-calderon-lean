import Proof.WeakFirstPoissonEnergy
import Proof.NativeWeakCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

lemma nativeCoefficientEnergy_multiplier_forcing (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F) 0 0
      (nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q) u) (v:BallH1)-
    TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F) 0 0 u
      (nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q) (v:BallH1)) =
    -⟪nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q u,
      TauCeti.W1p.value (v:BallH1)⟫_ℝ := by
  let Q2 := smoothMultiplierLowerJets Q
  let m := coefficientSmoothData Q2
  obtain ⟨B,hB,hm,hg⟩ := exists_smooth_ball_multiplier_bound m
  have hS (w : BallH1) := nativeCoefficientH1ProductL_eq_contDiffSMulL fixedSobolevCalculus Q2 hB hm hg w
  have h := nativeEnergy_smooth_multiplier_difference_integral (coefficientMatrixField 2 F) 0 0 ha m hB hm hg u (v:BallH1)
  rw [← hS,← hS] at h
  have hDatum : m = ⟨coefficientValue 3 Q,contDiff_coefficientValue 3 Q⟩ := by
    apply Subtype.ext
    exact coefficientValue_smoothMultiplierLowerJets Q
  have hG : nativeSmoothDriftField (fun _ : I => (0:SmoothCoefficientJets 1)) = (0:X → X) := by ext z j;rfl
  have hResidual := nativeBulkMultiplierEnergyResidual_eq_neg_forcing fixedSobolevCalculus F (fun _ => 0) Q u v
  rw [← hDatum,hG] at hResidual
  exact h.trans hResidual

def weakFirstMultiplierDefectL (F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  let W1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  let M := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  let S := nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q)
  W1.comp M-S.comp W1

lemma weakFirstMultiplierDefect_mem_zero (F1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (1/2:ℝ)) :
    weakFirstMultiplierDefectL F1 ha1 Q f ∈ TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
  apply (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.sub_mem
  · exact weakFirstPoissonVariation_mem_zero 1 ha1 _
  · exact nativeCoefficientH1Product_mem_zero _ ⟨_,weakFirstPoissonVariation_mem_zero 1 ha1 f⟩

/-- Exact linearized multiplier defect equation. The coefficient forcing
and the inverse variation are retained with their actual common witnesses. -/
theorem weakFirstMultiplierDefect_energy (F0 F1 : SmoothCoefficientMatrix 2)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F0) 0 0
      (weakFirstMultiplierDefectL F1 ha1 Q f) (v:BallH1) =
    ⟪nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
      (weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1 f),TauCeti.W1p.value (v:BallH1)⟫_ℝ+
    ⟪nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F1 (fun _ => 0) Q
      (fixedHarmonicH1LiftL f),TauCeti.W1p.value (v:BallH1)⟫_ℝ-
    TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F1) 0 0
      (weakPoissonMultiplierDefectL F0 ha0 Q f) (v:BallH1) := by
  let W1 := weakFirstPoissonVariationL 1 (coefficientMatrixField 2 F1) ha1
  let M := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  let S := nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q)
  let E0 := nativeCoefficientWeakEnergyL (coefficientMatrixField 2 F0) 0 0 ha0
  let E1 := nativeCoefficientWeakEnergyL (coefficientMatrixField 2 F1) 0 0 ha1
  have hW0 : nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner = fixedHarmonicH1LiftL :=
    (nativeWeakHalfLift_congr_unitBall ha0 (flatCoefficientBound 1) (by intro z hz;simpa using hFlat z hz)).trans
      (nativeWeakHalfLift_flat_eq 1 (flatCoefficientBound 1))
  have hW1 (g : SphereSobolev (1/2:ℝ)) (w : BallH1Zero) : E0 (W1 g) w = -E1 (fixedHarmonicH1LiftL g) w := by
    rw [nativeCoefficientWeakEnergyL_apply,nativeCoefficientWeakEnergyL_apply]
    exact (energyFormH1_congr_coeff_on (by intro z hz;simpa using hFlat z hz) (W1 g) (w:BallH1)).trans
      (weakFirstPoissonVariation_energy 1 (by norm_num) ha1 g w)
  have hSv := nativeCoefficientH1Product_mem_zero (smoothMultiplierLowerJets Q) v
  have hWM := hW1 (M f) v
  have hWS := hW1 f ⟨S (v:BallH1),hSv⟩
  have hCancel0 := nativeCoefficientEnergy_multiplier_forcing F0 ha0 Q (W1 f) v
  have hCancel1 := nativeCoefficientEnergy_multiplier_forcing F1 ha1 Q (fixedHarmonicH1LiftL f) v
  have hSub0 := congrArg (fun w : StrongDual ℝ BallH1Zero => w v) (E0.map_sub (W1 (M f)) (S (W1 f)))
  have hSub1 := congrArg (fun w : StrongDual ℝ BallH1Zero => w v)
    (E1.map_sub (fixedHarmonicH1LiftL (M f)) (S (fixedHarmonicH1LiftL f)))
  simp only [E0,E1,sub_apply,nativeCoefficientWeakEnergyL_apply] at hSub0 hSub1 hWM hWS
  have hDefect : weakPoissonMultiplierDefectL F0 ha0 Q f = fixedHarmonicH1LiftL (M f)-S (fixedHarmonicH1LiftL f) := by
    change nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner (M f)-
      S (nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 ha0 sphereFischerInner f) = _
    rw [hW0]
  rw [hDefect]
  change TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F0) 0 0
    (W1 (M f)-S (W1 f)) (v:BallH1) = _
  linarith

end ShrinkingSpheres
