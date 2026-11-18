import Proof.WeakPoissonTaylor
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

def nativeWeakPoissonZeroFirstRemainderL (a a1 : X → Mat)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (c r : ℝ) : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1Zero :=
  (nativeZeroCoefficientEnergyL a 0 0 ha).inverse.comp
    ((nativeCoefficientWeakEnergyL a 0 0 ha).comp fixedHarmonicH1LiftL)-
  r • (nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).inverse.comp
    ((nativeCoefficientWeakEnergyL a1 0 0 ha1).comp fixedHarmonicH1LiftL)

/-- The actual weak bulk Taylor remainder is the negative inclusion of its
    same native zero-boundary correction; no arbitrary solution is selected. -/
theorem nativeWeakHalfLift_first_remainder_eq_zero (a a1 : X → Mat)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (c r : ℝ) :
    nativeWeakHalfLift a 0 0 ha sphereFischerInner-fixedHarmonicH1LiftL-r • weakFirstPoissonVariationL c a1 ha1 =
      -((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
        (nativeWeakPoissonZeroFirstRemainderL a a1 ha ha1 c r)) := by
  let j : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let A := nativeZeroCoefficientEnergyL a 0 0 ha
  let A0 := nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T := nativeCoefficientWeakEnergyL a 0 0 ha
  let T1 := nativeCoefficientWeakEnergyL a1 0 0 ha1
  have hI : A.inverse = nativeCoefficientWeakFunctionalInverse a 0 0 ha :=
    nativeZeroCoefficientEnergy_inverse_eq ha
  have hI0 : A0.inverse = nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c) :=
    nativeZeroCoefficientEnergy_inverse_eq _
  have hLiftEq : nativeWeakHalfLift a 0 0 ha sphereFischerInner =
      fixedHarmonicH1LiftL-j.comp (A.inverse.comp (T.comp fixedHarmonicH1LiftL)) :=
    (nativeWeakHalfLift_native_assembly ha).trans (congrArg
      (fun I0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero =>
        fixedHarmonicH1LiftL-j.comp (I0.comp (T.comp fixedHarmonicH1LiftL))) hI.symm)
  have hFirstEq : weakFirstPoissonVariationL c a1 ha1 =
      -(j.comp (A0.inverse.comp (T1.comp fixedHarmonicH1LiftL))) :=
    congrArg (fun I0 : StrongDual ℝ BallH1Zero →L[ℝ] BallH1Zero =>
      -(j.comp (I0.comp (T1.comp fixedHarmonicH1LiftL)))) hI0.symm
  have hResult := congrArg₂ (fun Pa P1 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 =>
    Pa-fixedHarmonicH1LiftL-r • P1) hLiftEq hFirstEq
  refine hResult.trans ?_
  change fixedHarmonicH1LiftL-j.comp (A.inverse.comp (T.comp fixedHarmonicH1LiftL))-
    fixedHarmonicH1LiftL-r • -(j.comp (A0.inverse.comp (T1.comp fixedHarmonicH1LiftL))) =
    -(j.comp (A.inverse.comp (T.comp fixedHarmonicH1LiftL)-
      r • A0.inverse.comp (T1.comp fixedHarmonicH1LiftL)))
  simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
  module

attribute [local irreducible] nativeWeakHalfLift weakFirstPoissonVariationL

lemma norm_nativeWeakPoissonZeroFirstRemainderL_le (a a1 : X → Mat)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (c r CS : ℝ) (hCS : 0 ≤ CS)
    (hNorm : ‖nativeWeakHalfLift a 0 0 ha sphereFischerInner-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c a1 ha1‖ ≤ CS) :
    ‖nativeWeakPoissonZeroFirstRemainderL a a1 ha ha1 c r‖ ≤ CS := by
  let J : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let S := nativeWeakPoissonZeroFirstRemainderL a a1 ha ha1 c r
  have hPost : ‖-(J.comp S)‖ ≤ CS := by
    have hEq := congrArg (fun M : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => ‖M‖)
      (nativeWeakHalfLift_first_remainder_eq_zero a a1 ha ha1 c r)
    exact hEq.symm.le.trans hNorm
  rw [norm_neg] at hPost
  apply ContinuousLinearMap.opNorm_le_bound _ hCS
  intro f
  exact ((J.comp S).le_opNorm f).trans (mul_le_mul_of_nonneg_right hPost (norm_nonneg f))

lemma norm_nativeWeakZeroInclusion_le_one :
    ‖((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL :
      BallH1Zero →L[ℝ] BallH1)‖ ≤ 1 := Submodule.norm_subtypeL_le _

/-- Native weak bulk remainder derivatives preserve quadratic smallness through
    the actual rectangular zero-energy inverse identity. -/
theorem norm_nativeWeakHalfLift_first_remainder_derivative_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a a1 : P → X → Mat)
    (ha : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand (a p z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 p z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (c r : ℝ) (x : P) (U : Set P) (hU : IsOpen U) (hx : x ∈ U)
    (hInv : ∀ p ∈ U,(nativeZeroCoefficientEnergyL (a p) 0 0 (ha p)).IsInvertible)
    (hInv0 : (nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).IsInvertible)
    (hA : DifferentiableAt ℝ (fun p => nativeZeroCoefficientEnergyL (a p) 0 0 (ha p)) x)
    (hT : DifferentiableAt ℝ (fun p => nativeCoefficientWeakEnergyL (a p) 0 0 (ha p)) x)
    (hT1 : DifferentiableAt ℝ (fun p => nativeCoefficientWeakEnergyL (a1 p) 0 0 (ha1 p)) x)
    (CI C0 DA DB V1 D1 DQ CS : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ) (hCS : 0 ≤ CS)
    (hNI : ‖(nativeZeroCoefficientEnergyL (a x) 0 0 (ha x)).inverse‖ ≤ CI)
    (hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).inverse‖ ≤ C0)
    (hNA : ‖fderiv ℝ (fun p => nativeZeroCoefficientEnergyL (a p) 0 0 (ha p)) x‖ ≤ DA*r)
    (hNB : ‖nativeZeroCoefficientEnergyL (a x) 0 0 (ha x)-
      nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ DB*r)
    (hNV1 : ‖nativeCoefficientWeakEnergyL (a1 x) 0 0 (ha1 x)‖ ≤ V1)
    (hND1 : ‖fderiv ℝ (fun p => nativeCoefficientWeakEnergyL (a1 p) 0 0 (ha1 p)) x‖ ≤ D1)
    (hNDQ : ‖fderiv ℝ (fun p => nativeCoefficientWeakEnergyL (a p) 0 0 (ha p)-
      nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)-
      r • nativeCoefficientWeakEnergyL (a1 p) 0 0 (ha1 p)) x‖ ≤ DQ*r^2)
    (hNorm : ‖nativeWeakHalfLift (a x) 0 0 (ha x) sphereFischerInner-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (a1 x) (ha1 x)‖ ≤ CS*r^2) :
    ‖fderiv ℝ (fun p => nativeWeakHalfLift (a p) 0 0 (ha p) sphereFischerInner-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (a1 p) (ha1 p)) x‖ ≤
      CI*((DQ+DA*C0*V1+DB*C0*D1)*‖fixedHarmonicH1LiftL‖+DA*CS)*r^2 := by
  let A := fun p => nativeZeroCoefficientEnergyL (a p) 0 0 (ha p)
  let A0 := nativeZeroCoefficientEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T := fun p => nativeCoefficientWeakEnergyL (a p) 0 0 (ha p)
  let T0 := nativeCoefficientWeakEnergyL (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  let T1 := fun p => nativeCoefficientWeakEnergyL (a1 p) 0 0 (ha1 p)
  let S := fun p => nativeWeakPoissonZeroFirstRemainderL (a p) (a1 p) (ha p) (ha1 p) c r
  let J : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  have hInvDiff : DifferentiableAt ℝ (fun p => (A p).inverse) x := by
    have hi : DifferentiableAt ℝ (fun D : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => D.inverse) (A x) :=
      ((hInv x hx).contDiffAt_map_inverse (n:=1)).differentiableAt (by norm_num)
    simpa only [Function.comp_def] using hi.comp x (show DifferentiableAt ℝ A x from hA)
  have hTH : DifferentiableAt ℝ (fun p => (T p).comp fixedHarmonicH1LiftL) x :=
    hT.clm_comp (differentiableAt_const fixedHarmonicH1LiftL)
  have hT1H : DifferentiableAt ℝ (fun p => (T1 p).comp fixedHarmonicH1LiftL) x :=
    hT1.clm_comp (differentiableAt_const fixedHarmonicH1LiftL)
  have hS : DifferentiableAt ℝ S x := by
    change DifferentiableAt ℝ (fun p => (A p).inverse.comp ((T p).comp fixedHarmonicH1LiftL)-
      r • A0.inverse.comp ((T1 p).comp fixedHarmonicH1LiftL)) x
    exact (hInvDiff.clm_comp hTH).sub
      (((differentiableAt_const A0.inverse).clm_comp hT1H).const_smul r)
  have hQ : DifferentiableAt ℝ (fun p => T p-T0-r • T1 p) x :=
    (hT.hasFDerivAt.sub_const T0).differentiableAt.sub (hT1.const_smul r)
  have hFlat : T0.comp fixedHarmonicH1LiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro v
    change T0 (fixedHarmonicH1LiftL f) v = 0
    dsimp only [T0]
    rw [nativeCoefficientWeakEnergyL_apply]
    exact fixedHarmonicH1Lift_flat_weak c f v
  have hSNorm : ‖S x‖ ≤ CS*r^2 :=
    norm_nativeWeakPoissonZeroFirstRemainderL_le (a x) (a1 x) (ha x) (ha1 x) c r (CS*r^2) (by positivity) hNorm
  have hBound := norm_poisson_taylor_remainder_derivative_le (P:=P) (Z:=BallH1Zero)
    (E:=BallH1) (F:=StrongDual ℝ BallH1Zero) (H:=SphereSobolev (1/2:ℝ))
    A A0 T T1 T0 fixedHarmonicH1LiftL S r x U hU hx
    hA hT1 hQ hS hInv hInv0 hFlat (fun p hp => rfl)
    CI C0 DA DB V1 D1 DQ CS hr hr1 hCI hC0 hDA hDB hV1 hD1 hDQ hCS
    hNI hNI0 hNA hNB hNV1 hND1 hNDQ hSNorm
  have hIdentity : (fun p => nativeWeakHalfLift (a p) 0 0 (ha p) sphereFischerInner-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (a1 p) (ha1 p)) = fun p => (-J).comp (S p) := by
    funext p
    exact (nativeWeakHalfLift_first_remainder_eq_zero (a p) (a1 p) (ha p) (ha1 p) c r).trans (by rw [ContinuousLinearMap.neg_comp])
  have hNormEq := congrArg (fun f : P → SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => ‖fderiv ℝ f x‖) hIdentity
  refine hNormEq.le.trans ?_
  have hD := norm_fderiv_clm_comp_le (P:=P) (E:=SphereSobolev (1/2:ℝ)) (F:=BallH1Zero) (G:=BallH1) (fun _ : P => -J) S x (differentiableAt_const (-J)) hS
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hD
  have hJ : ‖-J‖ ≤ 1 := by
    rw [norm_neg]
    exact norm_nativeWeakZeroInclusion_le_one
  exact hD.trans ((mul_le_mul hJ hBound (norm_nonneg _) zero_le_one).trans_eq (by ring))

end ShrinkingSpheres
