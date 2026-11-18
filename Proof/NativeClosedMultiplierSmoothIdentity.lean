import Proof.CommonSupportClosedMovingMultiplierHigherJets
import Proof.CommonSupportMovingMultiplierIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
local instance : CompleteSpace (SphereSobolev (1/2:ℝ)) := lp.completeSpace
local instance : CompleteSpace (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) := by infer_instance

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem commonSupportNativeClosedMultiplierKernel_on_smooth
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P) (Q : SmoothCoefficientJets 3) :
    commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p
      (smoothCoefficientClosureInclusionL 3 Q) =
    commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p Q :=
  (commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p).extend_eq
    (denseRange_smoothCoefficientClosureInclusionL 3)
    (show IsUniformInducing (smoothCoefficientClosureInclusionL 3) from (show Isometry (smoothCoefficientClosureInclusionL 3) from fun _ _ => rfl).isUniformInducing) Q

/-- Completed smooth multiplier families evaluate to the original actual
    commutator, without assuming smoothness into the nonclosed smooth subspace. -/
theorem commonSupport_closed_multiplier_family_eq_actual_commutator
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
      ((volume:Measure X).restrict ballOpens))
    (b : P × X → ℝ) (hb : ContDiff ℝ ∞ b) (SQ : Set X) (hSQ : IsCompact SQ)
    (hzb : ∀ p z,z ∉ SQ → b (p,z) = 0) (r : ℝ) :
    (fun t => commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t
      (commonSupportClosedCoefficientFamily 3 b hb SQ hSQ hzb t)) =
    (fun t => radialTaylorMultiplierCommutatorL
      (commonSupportMatrixFamily 2 a ha S hS hz t) F0 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)
      (hMem t) hMem0 (hMem1 t) (commonSupportCoefficientFamily 3 b hb SQ hSQ hzb t) r) := by
  funext t
  rw [commonSupportClosedCoefficientFamily,commonSupportNativeClosedMultiplierKernel_on_smooth]
  exact (congrFun (commonSupport_moving_multiplier_commutator_eq_curried_kernel a a1 ha ha1 S S1 hS hS1 hz hz1
    F0 hFlat hMem hMem1 hMem0 (commonSupportCoefficientFamily 3 b hb SQ hSQ hzb) r) t).symm

end ShrinkingSpheres
