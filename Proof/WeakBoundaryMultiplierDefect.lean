import Proof.Archive.NativeSmoothMultiplierForcingEnergy
import Proof.Archive.NativeH2SmoothMultiplierOutwardTrace
import Proof.WeakStrongPoissonCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Gradient
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.NativeFullSharpHalfTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse nativeCoefficientWeakFunctionalInverse

/-- The same actual weak Poisson lift has the canonical half-order value trace. -/
theorem fixedHalfValueTrace_nativeWeakHalfLift {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (f : SphereSobolev (1/2:ℝ)) :
    fixedHalfValueTraceL (nativeWeakHalfLift a 0 0 ha sphereFischerInner f) = f := by
  let W := nativeWeakHalfLift a 0 0 ha sphereFischerInner
  let v : BallH1Zero := ⟨fixedHarmonicH1LiftL f-W f,nativeWeakHalfLift_affine_difference a 0 0 ha sphereFischerInner f⟩
  have hZero := nativeHalfTraceL_zeroDirichlet sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace v
  change fixedHalfValueTraceL (fixedHarmonicH1LiftL f-W f) = 0 at hZero
  rw [map_sub] at hZero
  have hFlat : fixedHalfValueTraceL (fixedHarmonicH1LiftL f) = f :=
    congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T f) fixedHalfValueTrace_right_inverse
  exact (sub_eq_zero.mp hZero).symm.trans hFlat

def weakPoissonMultiplierDefectL (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  let W := nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner
  W.comp (nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace (smoothMultiplierLowerJets Q))-
  (nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q)).comp W

/-- Multiplication commutes with the actual boundary value trace, so the
same Poisson multiplication defect has genuine zero Dirichlet boundary. -/
theorem weakPoissonMultiplierDefect_zero_boundary (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) (f : SphereSobolev (1/2:ℝ)) :
    weakPoissonMultiplierDefectL F ha Q f ∈ TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
  let W := nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner
  let M := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  let S := nativeCoefficientH1ProductL fixedSobolevCalculus (smoothMultiplierLowerJets Q)
  have hProduct : fixedHalfValueTraceL (S (W f)) = M (fixedHalfValueTraceL (W f)) :=
    nativeHalfTraceL_coefficientH1Product fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      fixedUnitBallValueTrace (smoothMultiplierLowerJets Q) (W f)
  have hHalf : fixedHalfValueTraceL (weakPoissonMultiplierDefectL F ha Q f) = 0 := by
    change fixedHalfValueTraceL (W (M f)-S (W f)) = 0
    rw [map_sub,hProduct,fixedHalfValueTrace_nativeWeakHalfLift,fixedHalfValueTrace_nativeWeakHalfLift,sub_self]
  have hValue : fixedUnitBallValueTrace.valueTraceL (weakPoissonMultiplierDefectL F ha Q f) = 0 := by
    apply (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).injective
    have h := congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)) hHalf
    simpa only [fixedHalfValueTraceL,sphereSobolevInclusionL_nativeHalfTraceL,map_zero] using h
  exact (fixedUnitBallValueTrace_kernel _).mp hValue

/-- The actual weak multiplication defect solves the exact first-order
bulk commutator forcing equation, for arbitrary genuine coefficients. -/
theorem weakPoissonMultiplierDefect_energy_forcing (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha)) (Q : SmoothCoefficientJets 3)
    (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) (coefficientMatrixField 2 F) 0 0
      (weakPoissonMultiplierDefectL F ha Q f) (v:BallH1) =
      ⟪nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q
        (nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner f),TauCeti.W1p.value (v:BallH1)⟫_ℝ := by
  let a := coefficientMatrixField 2 F
  let W := nativeWeakHalfLift a 0 0 ha sphereFischerInner
  let Q2 := smoothMultiplierLowerJets Q
  let m := coefficientSmoothData Q2
  let M := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q2
  let S := nativeCoefficientH1ProductL fixedSobolevCalculus Q2
  obtain ⟨C,hC,hm,hg⟩ := exists_smooth_ball_multiplier_bound m
  have hS (u : BallH1) : S u = TauCeti.W1p.contDiffSMulL m.1 m.2 hC hm hg u :=
    nativeCoefficientH1ProductL_eq_contDiffSMulL fixedSobolevCalculus Q2 hC hm hg u
  have hSv : S (v:BallH1) ∈ TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
    rw [hS,TauCeti.W1p.contDiffSMulL_apply]
    exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule m.2 hC hm hg v.property
  have hWeak (g : SphereSobolev (1/2:ℝ)) (w : BallH1Zero) :
      TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) a 0 0 (W g) (w:BallH1) = 0 :=
    nativeWeakHalfLift_weak_solution a 0 0 ha sphereFischerInner (isInvertible_of_bilinear_coercive _ hc) g w
  have hu := hWeak f ⟨S (v:BallH1),hSv⟩
  have hu' := hWeak (M f) v
  have hCancel := nativeEnergy_smooth_multiplier_difference_integral a 0 0 ha m hC hm hg (W f) (v:BallH1)
  rw [← hS,← hS] at hCancel
  let E := nativeCoefficientWeakEnergyL a 0 0 ha
  have hSub := congrArg (fun ell : StrongDual ℝ BallH1Zero => ell v) (E.map_sub (W (M f)) (S (W f)))
  have hE (u : BallH1) : E u v = TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) a 0 0 u (v:BallH1) :=
    nativeCoefficientWeakEnergyL_apply a 0 0 ha u v
  simp only [sub_apply,hE] at hSub
  have hDatum : m = ⟨coefficientValue 3 Q,contDiff_coefficientValue 3 Q⟩ := by
    apply Subtype.ext
    exact coefficientValue_smoothMultiplierLowerJets Q
  have hG : nativeSmoothDriftField (fun _ : I => (0:SmoothCoefficientJets 1)) = (0:X → X) := by ext z j;rfl
  have hResidual := nativeBulkMultiplierEnergyResidual_eq_neg_forcing fixedSobolevCalculus F (fun _ => 0) Q (W f) v
  rw [← hDatum,hG] at hResidual
  change TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) a 0 0 (W (M f)-S (W f)) (v:BallH1) = _
  change TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) a 0 0 (W f) (S (v:BallH1)) = 0 at hu
  linarith

end ShrinkingSpheres
