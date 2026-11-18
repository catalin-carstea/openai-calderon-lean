import Proof.CommonSupportWeakTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse

variable {Param : Type} [NormedAddCommGroup Param] [NormedSpace ℝ Param] [FiniteDimensional ℝ Param]

/-- The normalized weak point packet transfers to the raw families by exact
coefficient equality, without changing any quantitative constant. -/
theorem commonSupport_native_weak_point_transfer
    (A A1 : Param × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → A (t,z) = 0) (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0)
    (r CW CA P Q CP1 CP2 : ℝ)
    (hPoint : NativeWeakTaylorData
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz 0))
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 0))
      1 r CW CA P Q CP1 CP2) :
    NativeWeakTaylorData (fun z => A (0,z)) (fun z => A1 (0,z))
      1 r CW CA P Q CP1 CP2 := by
  simpa only [coefficientMatrixField_commonSupportMatrixFamily] using hPoint

/-- Raw and compact-family weak lifts are the SAME maps. The MemLp witnesses
are proofs, so they introduce no extra choice when the coefficient is rewritten. -/
theorem commonSupport_native_weak_lift_family_eq
    (A : Param × X → Mat) (hA : ContDiff ℝ ∞ A) (S : Set X) (hS : IsCompact S)
    (hz : ∀ t z,z ∉ S → A (t,z) = 0)
    (hMem : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    (fun t => nativeWeakHalfLift
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A hA S hS hz t)) 0 0
      (hMem t) sphereFischerInner) = commonSupportWeakHalfLift A hA := by
  funext t
  simp only [coefficientMatrixField_commonSupportMatrixFamily]
  rfl

/-- The first weak variation uses exactly the same raw first coefficient. -/
theorem commonSupport_native_weak_first_family_eq
    (A1 : Param × X → Mat) (hA1 : ContDiff ℝ ∞ A1) (S : Set X) (hS : IsCompact S)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0)
    (hMem : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    (fun t => weakFirstPoissonVariationL 1
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 A1 hA1 S hS hz1 t)) (hMem t)) =
      fun t => weakFirstPoissonVariationL 1 (fun z => A1 (t,z)) (commonSupportEnergyMemLp A1 hA1 t) := by
  funext t
  simp only [coefficientMatrixField_commonSupportMatrixFamily]

end ShrinkingSpheres
