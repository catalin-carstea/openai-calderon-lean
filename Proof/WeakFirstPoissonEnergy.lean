import Proof.ConormalSymmetry
import Proof.WeakStrongFirstVariation
import Proof.WeakBoundaryMultiplierDefect

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
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

/-- The genuine first weak Poisson correction solves the linearized
Dirichlet energy equation against every zero-boundary test. -/
theorem weakFirstPoissonVariation_energy (c : ℝ) (hc : 0 < c) {a1 : X → Mat}
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (f : SphereSobolev (1/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (fun _ : X => c • (1:Mat)) 0 0 (weakFirstPoissonVariationL c a1 ha1 f) (v:BallH1) =
      -TauCeti.PDE.energyFormH1 (mu:=(volume:Measure X)) (Omega:=ballOpens) a1 0 0
        (fixedHarmonicH1LiftL f) (v:BallH1) := by
  let A0 := TauCeti.PDE.energyFormH1L0 (flatCoefficientBound c)
  let ell := nativeCoefficientWeakEnergyL a1 0 0 ha1 (fixedHarmonicH1LiftL f)
  let I0 := nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  have hInv := canonicalWeakEnergy_isInvertible (a:=fun _ : X => c • (1:Mat)) (flatCoefficientBound c)
    (flat_native_weak_energy_data c hc).coercive
  have hI : I0 = A0.inverse := nativeCoefficientWeakFunctionalInverse_eq_inverse (flatCoefficientBound c)
  have hSolve : A0 (I0 ell) = ell := by rw [hI,hInv.self_apply_inverse]
  have hScalar := congrArg (fun w : StrongDual ℝ BallH1Zero => w v) (A0.map_neg (I0 ell))
  rw [hSolve] at hScalar
  change A0 (-(I0 ell)) v = -(ell v) at hScalar
  rw [TauCeti.PDE.energyFormH1L0_apply,nativeCoefficientWeakEnergyL_apply] at hScalar
  exact hScalar

/-- The same native H1 multiplication preserves the actual zero trace. -/
theorem nativeCoefficientH1Product_mem_zero (Q : SmoothCoefficientJets 2) (v : BallH1Zero) :
    nativeCoefficientH1ProductL fixedSobolevCalculus Q (v:BallH1) ∈
      TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
  let m := coefficientSmoothData Q
  obtain ⟨B,hB,hm,hg⟩ := exists_smooth_ball_multiplier_bound m
  rw [nativeCoefficientH1ProductL_eq_contDiffSMulL fixedSobolevCalculus Q hB hm hg,
    TauCeti.W1p.contDiffSMulL_apply]
  exact TauCeti.W1p.contDiffSMul_mem_w1p0Submodule m.2 hB hm hg v.property

end ShrinkingSpheres
