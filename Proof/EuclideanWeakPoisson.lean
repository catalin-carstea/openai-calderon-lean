import Proof.StrongPoissonIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open OAI.AnisotropicCalderon.NativeHarmonicLiftCompletion
open OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence

/-- The completed H1 Euclidean Poisson lift is weakly harmonic, proved on the
    dense finite harmonic core using the checked strong flat kernel. -/
theorem fixedHarmonicH1Lift_flat_weak (c : ℝ) (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (fun _ : X => c • (1:Mat)) (fun _ => (0:X)) (fun _ => (0:ℝ))
      (fixedHarmonicH1LiftL f) (v : BallH1) = 0 := by
  let hcoeff : MemLp (fun _ : X => TauCeti.PDE.energyIntegrand (c • (1:Mat)) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens) := memLp_top_const _
  let E := TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=fun _ : X => c • (1:Mat)) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
  let T : SphereSobolev (1/2:ℝ) →L[ℝ] ℝ := (E.flip (v : BallH1)).comp fixedHarmonicH1LiftL
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix 2
  have hF0Ball (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientMatrixField 2 F0 x = 1 :=
    hF0 x (unitBall_subset_closedBall_two hx)
  have hField (x : X) (hx : x ∈ (ballOpens : Set X)) : coefficientMatrixField 2 (c • F0) x = c • (1:Mat) := by
    rw [coefficientMatrixField_smul,hF0Ball x hx]
  have hEq : (T : SphereSobolev (1/2:ℝ) → ℝ) = fun _ => 0 := by
    apply denseRange_harmonicHalfBoundaryFiniteL.equalizer T.continuous continuous_const
    funext a
    have hP : fixedHarmonicH1LiftL (harmonicHalfBoundaryFiniteL a) =
        TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL (harmonicBoundaryFiniteL a)) := by
      symm
      change TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion sphereFischerInner (harmonicBoundaryFiniteL a)) =
        harmonicFirstOrderLiftCompletion sphereFischerInner (harmonicHalfBoundaryFiniteL a)
      rw [firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics,
        sphereSobolevInclusionL_harmonicBoundaryFiniteL]
    have hFlat : fullCoefficientOperatorL fixedSobolevCalculus 0 (c • F0)
        (fixedHarmonicLiftL (harmonicBoundaryFiniteL a)) = 0 :=
      fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner
        orthogonalSphereHarmonics F0 hF0Ball c (harmonicBoundaryFiniteL a)
    have hEnergy := fullCoefficientOperator_energy fixedSobolevCalculus 0 (c • F0)
      (fixedHarmonicLiftL (harmonicBoundaryFiniteL a)) v
    rw [hFlat,TauCeti.Wkp.value_zero,TauCeti.PDE.dirichletForcing_apply,inner_zero_left] at hEnergy
    change E (fixedHarmonicH1LiftL (harmonicHalfBoundaryFiniteL a)) (v : BallH1) = 0
    rw [TauCeti.PDE.energyFormH1L_apply,hP]
    exact (energyFormH1_congr_coeff_on hField _ (v : BallH1)).symm.trans hEnergy.symm
  have hTf := congr_fun hEq f
  change E (fixedHarmonicH1LiftL f) (v : BallH1) = 0 at hTf
  rw [TauCeti.PDE.energyFormH1L_apply] at hTf
  exact hTf

end ShrinkingSpheres
