import Proof.Archive.NativeCoefficientWeakEnergy
import Proof.Archive.InheritedNormedStructureData
import Proof.Archive.ClmInheritedStructureData
import Proof.Archive.LpInheritedStructureData

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def nativeZeroCoefficientEnergyL
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ := by
  have h := TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := b) (c := c) hcoeff
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at h
  exact h

lemma nativeZeroCoefficientEnergyL_apply
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1Zero) :
    nativeZeroCoefficientEnergyL a b c hcoeff u v =
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff u v := rfl

lemma nativeZeroCoefficientEnergyL_isInvertible_iff
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    (nativeZeroCoefficientEnergyL a b c hcoeff).IsInvertible ↔
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff).IsInvertible := by
  rfl


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
