import Proof.CommonSupportCurriedMultiplierKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The curried moving-input kernel is the original actual commutator for
    the same coefficient, first model and native MemLp witnesses. -/
theorem commonSupport_moving_multiplier_commutator_eq_curried_kernel
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hMem : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hMem1 : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hMem0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : P → SmoothCoefficientJets 3) (r : ℝ) :
    (fun t => radialTaylorMultiplierCommutatorL
      (commonSupportMatrixFamily 2 a ha S hS hz t) F0 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)
      (hMem t) hMem0 (hMem1 t) (Q t) r) =
    (fun t => commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t (Q t)) := by
  funext t
  exact (congrFun (commonSupport_radialTaylorMultiplierCommutator_eq_kernel a a1 ha ha1 S S1 hS hS1 hz hz1
    F0 hFlat hMem hMem1 hMem0 (Q t) r) t).trans
      (commonSupportNativeMultiplierKernelInMultiplierL_apply a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t (Q t)).symm

end ShrinkingSpheres
