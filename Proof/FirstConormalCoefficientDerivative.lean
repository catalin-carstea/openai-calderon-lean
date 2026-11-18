import Proof.ConormalSymmetry
import Proof.ConormalEnergyDerivative
import Proof.CommonSupportWeakPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The flat solution variation vanishes against the fixed harmonic test, so
    the actual first conormal map is the first coefficient energy alone. -/
theorem weakFirstConormal_eq_coefficient_energy (c : ℝ) {a1 : X → Mat}
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    weakFirstConormalVariationL c a1 ha1 = (sphereSobolevDualRieszL (1/2:ℝ)).comp
      (sphereSurfaceMass⁻¹ • (TauCeti.PDE.energyFormH1L ha1).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL) := by
  have hz : (TauCeti.PDE.energyFormH1L (flatCoefficientBound c)).bilinearComp
      (weakFirstPoissonVariationL c a1 ha1) fixedHarmonicH1LiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    apply ContinuousLinearMap.ext
    intro g
    change TauCeti.PDE.energyFormH1L (flatCoefficientBound c)
      (weakFirstPoissonVariationL c a1 ha1 f) (fixedHarmonicH1LiftL g) = 0
    exact (TauCeti.PDE.energyFormH1L_apply (flatCoefficientBound c) _ _).trans
      (flatEnergy_firstPoisson_test_eq_zero c ha1 f g)
  unfold weakFirstConormalVariationL
  rw [hz,zero_add]

/-- The genuine first conormal family's derivative requires only the actual
    first coefficient energy derivative, and no derivative of a chosen inverse. -/
theorem commonSupport_weakFirstConormal_coefficient_derivative
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (c : ℝ) (x : P)
    (hE : DifferentiableAt ℝ (commonSupportFullWeakEnergy a1 ha1) x)
    (DE : ℝ) (hDE : 0 ≤ DE) (hNE : ‖fderiv ℝ (commonSupportFullWeakEnergy a1 ha1) x‖ ≤ DE) :
    DifferentiableAt ℝ (fun p => weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) x ∧
    ‖fderiv ℝ (fun p => weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) x‖ ≤
      sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖^2*DE := by
  let H0 := fixedHarmonicH1LiftL
  let E := commonSupportFullWeakEnergy a1 ha1
  let Pre := fun p => (E p).comp H0
  let Post : (BallH1 →L[ℝ] ℝ) →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev (1/2:ℝ)) BallH1 ℝ).flip H0
  let Q := fun p => Post.comp (Pre p)
  let SQ := fun p => sphereSurfaceMass⁻¹ • Q p
  let N := fun p => (sphereSobolevDualRieszL (1/2:ℝ)).comp (SQ p)
  have hPre : DifferentiableAt ℝ Pre x := hE.clm_comp (differentiableAt_const H0)
  have hQ : DifferentiableAt ℝ Q x := (differentiableAt_const Post).clm_comp hPre
  have hSQ : DifferentiableAt ℝ SQ x := hQ.const_smul sphereSurfaceMass⁻¹
  have hN : DifferentiableAt ℝ N x := (differentiableAt_const _).clm_comp hSQ
  have hPost : ‖Post‖ ≤ ‖H0‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ell
    exact (ContinuousLinearMap.opNorm_comp_le ell H0).trans_eq (mul_comm _ _)
  have hDP := norm_fderiv_clm_comp_le E (fun _ : P => H0) x hE (differentiableAt_const H0)
  simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at hDP
  have hPreBound : ‖fderiv ℝ Pre x‖ ≤ DE*‖H0‖ :=
    hDP.trans (mul_le_mul_of_nonneg_right hNE (norm_nonneg _))
  have hDQ := norm_fderiv_clm_comp_le (fun _ : P => Post) Pre x (differentiableAt_const Post) hPre
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hDQ
  have hQBound : ‖fderiv ℝ Q x‖ ≤ ‖H0‖*(DE*‖H0‖) :=
    hDQ.trans (mul_le_mul hPost hPreBound (norm_nonneg _) (norm_nonneg _))
  have hArea : 0 ≤ sphereSurfaceMass⁻¹ := inv_nonneg.mpr sphereSurfaceMass_pos.le
  have hSQBound : ‖fderiv ℝ SQ x‖ ≤ sphereSurfaceMass⁻¹*‖H0‖^2*DE := by
    have hD := (hQ.hasFDerivAt.const_smul sphereSurfaceMass⁻¹).fderiv
    change fderiv ℝ SQ x = _ at hD
    rw [hD,norm_smul,Real.norm_eq_abs,abs_of_nonneg hArea]
    exact (mul_le_mul_of_nonneg_left hQBound hArea).trans_eq (by ring)
  have hRiesz : ‖sphereSobolevDualRieszL (1/2:ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ell
    rw [norm_sphereSobolevDualRieszL_apply,one_mul]
  have hDN := norm_fderiv_clm_comp_le (fun _ : P => sphereSobolevDualRieszL (1/2:ℝ)) SQ x
    (differentiableAt_const _) hSQ
  simp only [fderiv_const_apply,norm_zero,zero_mul,zero_add] at hDN
  have hNBound : ‖fderiv ℝ N x‖ ≤ sphereSurfaceMass⁻¹*‖H0‖^2*DE :=
    hDN.trans ((mul_le_mul hRiesz hSQBound (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hFamily : (fun p => weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) = N := by
    funext p
    rw [weakFirstConormal_eq_coefficient_energy]
    change (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ • (E p).bilinearComp H0 H0) = N p
    congr 2
  rw [hFamily]
  exact ⟨hN,hNBound⟩

end ShrinkingSpheres
