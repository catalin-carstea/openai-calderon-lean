import Proof.WeakBoundaryMultiplierDefect
import Proof.StrongPoissonPerturbation
import Proof.Archive.StrongOperatorEnergy

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
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse nativeCoefficientWeakFunctionalInverse

def strongPoissonMultiplierDefectL (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallSobolev 2 :=
  fixedStrongH2InclusionL.comp ((strongDirichletOperator fixedSobolevCalculus 0 F).inverse.comp
    ((nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q).comp
      (nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner)))

/-- The strong inverse applied to the actual multiplier forcing is the
SAME zero-boundary weak Poisson defect, by genuine energy uniqueness. -/
theorem firstOrder_strongPoissonMultiplierDefect (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (Q : SmoothCoefficientJets 3) (f : SphereSobolev (1/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (strongPoissonMultiplierDefectL F ha Q f) = weakPoissonMultiplierDefectL F ha Q f := by
  let g : BallSobolev 0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q
    (nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner f)
  let U := (strongDirichletOperator fixedSobolevCalculus 0 F).inverse g
  let V : BallH1Zero := ⟨weakPoissonMultiplierDefectL F ha Q f,weakPoissonMultiplierDefect_zero_boundary F ha Q f⟩
  have hV : V = TauCeti.PDE.weakSolutionDirichlet ha hc g := by
    apply TauCeti.PDE.eq_weakSolutionDirichlet ha hc
    intro v
    simpa only [Pi.zero_def,V,g,TauCeti.PDE.dirichletForcing_apply] using weakPoissonMultiplierDefect_energy_forcing F ha hc Q f v
  have hU : strongDirichletProjectionL 0 U = TauCeti.PDE.weakSolutionDirichlet ha hc g := by
    apply TauCeti.PDE.eq_weakSolutionDirichlet ha hc
    intro v
    have hAU : strongDirichletOperator fixedSobolevCalculus 0 F U = g := hInv.self_apply_inverse g
    have hEnergy := (strongCoefficientOperator_energy fixedSobolevCalculus 0 F U v).symm
    rw [hAU] at hEnergy
    simpa only [Nat.zero_add,Pi.zero_def,TauCeti.Wkp.value_zero] using hEnergy
  have hSame := congrArg (fun w : BallH1Zero => (w:BallH1)) (hU.trans hV.symm)
  exact hSame

/-- Quantitative gain from half-order boundary data to an actual H2 bulk
multiplication defect, with explicit SAME inverse/forcing/weak-lift factors. -/
theorem norm_strongPoissonMultiplierDefectL_le (F : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) :
    ‖strongPoissonMultiplierDefectL F ha Q‖ ≤ ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖*
      ‖nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q‖*
      ‖nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner‖ := by
  let A := (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
  let K := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q
  let W := nativeWeakHalfLift (coefficientMatrixField 2 F) 0 0 ha sphereFischerInner
  have hj : ‖fixedStrongH2InclusionL‖ ≤ 1 := Submodule.norm_subtypeL_le _
  calc
    _ ≤ ‖fixedStrongH2InclusionL‖*‖A.comp (K.comp W)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(‖A‖*(‖K‖*‖W‖)) := mul_le_mul hj
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg A))) (norm_nonneg _) zero_le_one
    _ = _ := by ring

end ShrinkingSpheres
