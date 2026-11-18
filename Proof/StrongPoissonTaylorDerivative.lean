import Proof.PoissonTaylorDerivative
import Proof.StrongPoissonTaylorBounds
import Proof.CommonSupportPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

/-- The actual zero-boundary bulk correction after its true first variation. -/
def strongPoissonZeroFirstRemainderL (F F0 F1 : SmoothCoefficientMatrix 2) (c r : ℝ) :
    SphereSobolev (3/2:ℝ) →L[ℝ] StrongDirichletSpace 0 :=
  (strongDirichletOperator fixedSobolevCalculus 0 F).inverse.comp
    ((fullCoefficientOperatorL fixedSobolevCalculus 0 F).comp fixedHarmonicLiftL)-
  r • (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse.comp
    ((fullCoefficientOperatorL fixedSobolevCalculus 0 F1).comp fixedHarmonicLiftL)

lemma strongPoisson_first_remainder_eq_zero (F F0 F1 : SmoothCoefficientMatrix 2) (c r : ℝ) :
    strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c =
      -(fixedStrongH2InclusionL.comp (strongPoissonZeroFirstRemainderL F F0 F1 c r)) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sub_apply,smul_apply,neg_apply,ContinuousLinearMap.comp_apply,
    strongPoissonL_apply,strongFirstPoissonVariationL,strongPoissonZeroFirstRemainderL,map_sub,map_smul]
  change fixedHarmonicLiftL f-fixedStrongH2InclusionL
      ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 F (fixedHarmonicLiftL f)))-
    fixedHarmonicLiftL f-r •
      (-fixedStrongH2InclusionL ((strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse
        (fullCoefficientOperatorL fixedSobolevCalculus 0 F1 (fixedHarmonicLiftL f)))) = _
  module

lemma norm_strongPoissonZeroFirstRemainderL_le (F F0 F1 : SmoothCoefficientMatrix 2) (c r CS : ℝ)
    (hCS : 0 ≤ CS)
    (hNorm : ‖strongPoissonL F-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 F1 c‖ ≤ CS) :
    ‖strongPoissonZeroFirstRemainderL F F0 F1 c r‖ ≤ CS := by
  rw [strongPoisson_first_remainder_eq_zero,norm_neg] at hNorm
  apply ContinuousLinearMap.opNorm_le_bound _ hCS
  intro f
  exact ((fixedStrongH2InclusionL.comp (strongPoissonZeroFirstRemainderL F F0 F1 c r)).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right hNorm (norm_nonneg f))

/-- Actual high radial Taylor remainders inherit the rectangular quadratic
    Poisson derivative estimate. All inverse and trace maps here are the native
    Dirichlet operators, not independent approximation witnesses. -/
theorem norm_actual_highRadial_first_remainder_derivative_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F F1 : P → SmoothCoefficientMatrix 2) (F0 : SmoothCoefficientMatrix 2) (c r : ℝ)
    (x : P) (U : Set P) (hU : IsOpen U) (hx : x ∈ U)
    (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hInv : ∀ p ∈ U,(strongDirichletOperator fixedSobolevCalculus 0 (F p)).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (hA : DifferentiableAt ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)) x)
    (hT : DifferentiableAt ℝ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)) x)
    (hT1 : DifferentiableAt ℝ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)) x)
    (CI C0 DA DB V1 D1 DQ CS : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hDQ : 0 ≤ DQ) (hCS : 0 ≤ CS)
    (hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 (F x)).inverse‖ ≤ CI)
    (hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ C0)
    (hNA : ‖fderiv ℝ (fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)) x‖ ≤ DA*r)
    (hNB : ‖strongDirichletOperator fixedSobolevCalculus 0 (F x)-
      strongDirichletOperator fixedSobolevCalculus 0 (c • F0)‖ ≤ DB*r)
    (hNV1 : ‖fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 x)‖ ≤ V1)
    (hND1 : ‖fderiv ℝ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)) x‖ ≤ D1)
    (hNDQ : ‖fderiv ℝ (fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)-
      fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)-
      r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)) x‖ ≤ DQ*r^2)
    (hNorm : ‖strongPoissonL (F x)-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 (F1 x) c‖ ≤ CS*r^2) :
    ‖fderiv ℝ (fun p => actualHighRadialErrorL (F p)-r • highFirstRadialVariationL F0 (F1 p) c) x‖ ≤
      ‖fixedHalfOutwardTraceL‖*CI*
        ((DQ+DA*C0*V1+DB*C0*D1)*‖fixedHarmonicLiftL‖+DA*CS)*r^2 := by
  let A := fun p => strongDirichletOperator fixedSobolevCalculus 0 (F p)
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 (c • F0)
  let T := fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F p)
  let T0 := fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)
  let T1 := fun p => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 p)
  let S := fun p => strongPoissonZeroFirstRemainderL (F p) F0 (F1 p) c r
  have hFlat : T0.comp fixedHarmonicLiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics F0 hF0 c f
  have hInvDiff : DifferentiableAt ℝ (fun p => (A p).inverse) x := by
    have hi : DifferentiableAt ℝ (fun D : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => D.inverse) (A x) :=
      ((hInv x hx).contDiffAt_map_inverse (n:=1)).differentiableAt (by norm_num)
    simpa only [Function.comp_def] using hi.comp x (show DifferentiableAt ℝ A x from hA)
  have hS : DifferentiableAt ℝ S x := (hInvDiff.clm_comp (hT.clm_comp
    (differentiableAt_const fixedHarmonicLiftL))).sub
      (((differentiableAt_const A0.inverse).clm_comp
        (hT1.clm_comp (differentiableAt_const fixedHarmonicLiftL))).const_smul r)
  have hQ := (hT.hasFDerivAt.sub_const T0).differentiableAt.sub (hT1.const_smul r)
  have hNS := norm_strongPoissonZeroFirstRemainderL_le (F x) F0 (F1 x) c r (CS*r^2) (by positivity) hNorm
  have hBound := norm_poisson_taylor_remainder_derivative_le A A0 T T1 T0 fixedHarmonicLiftL S r x U hU hx
    hA hT1 hQ hS hInv hInv0 hFlat (fun p hp => rfl)
    CI C0 DA DB V1 D1 DQ CS hr hr1 hCI hC0 hDA hDB hV1 hD1 hDQ hCS hNI hNI0 hNA hNB hNV1 hND1 hNDQ hNS
  let L := -(fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL)
  have hIdentity : (fun p => actualHighRadialErrorL (F p)-r • highFirstRadialVariationL F0 (F1 p) c) =
      fun p => L.comp (S p) := by
    funext p
    have hAlg : actualHighRadialErrorL (F p)-r • highFirstRadialVariationL F0 (F1 p) c =
        fixedHalfOutwardTraceL.comp
          (strongPoissonL (F p)-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 (F1 p) c) := by
      simp only [actualHighRadialErrorL,highFirstRadialVariationL,
        ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
    have hBulk := congrArg (fun M => fixedHalfOutwardTraceL.comp M)
      (strongPoisson_first_remainder_eq_zero (F p) F0 (F1 p) c r)
    exact hAlg.trans (hBulk.trans (by
      simp only [ContinuousLinearMap.comp_neg,ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.neg_comp,L,S]))
  rw [hIdentity]
  have hD := norm_fderiv_clm_comp_le (fun _ : P => L) S x (differentiableAt_const L) hS
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hD
  have hL : ‖L‖ ≤ ‖fixedHalfOutwardTraceL‖ := by
    change ‖-(fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL)‖ ≤ _
    rw [norm_neg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le _) (norm_nonneg _)).trans_eq (by ring))
  exact hD.trans ((mul_le_mul hL hBound (norm_nonneg _) (norm_nonneg _)).trans_eq (by ring))

end ShrinkingSpheres
