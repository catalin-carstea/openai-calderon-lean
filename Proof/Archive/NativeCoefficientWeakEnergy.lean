import Proof.Archive.NativeHarmonicH1LiftCompletion
import Proof.Archive.InheritedNormedStructureData
import Proof.Archive.ClmInheritedStructureData
import Proof.Archive.LpInheritedStructureData

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

 

variable (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
  (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
    ((volume : Measure R3).restrict ballOpens))

def nativeCoefficientWeakEnergyL : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  (TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
    (a := a) (b := b) (c := c) hcoeff).bilinearComp
      (ContinuousLinearMap.id ℝ BallH1)
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL

lemma nativeCoefficientWeakEnergyL_apply (u : BallH1) (v : BallH1Zero) :
    nativeCoefficientWeakEnergyL a b c hcoeff u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a b c u (v : BallH1) := by
  unfold nativeCoefficientWeakEnergyL
  rw [ContinuousLinearMap.bilinearComp_apply]
  exact TauCeti.PDE.energyFormH1L_apply hcoeff u (v : BallH1)

lemma nativeCoefficientWeakEnergyL_restriction (u v : BallH1Zero) :
    TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := a) (b := b) (c := c) hcoeff u v =
    nativeCoefficientWeakEnergyL a b c hcoeff (u : BallH1) v := by
  exact (TauCeti.PDE.energyFormH1L0_apply hcoeff u v).trans
    (nativeCoefficientWeakEnergyL_apply a b c hcoeff (u : BallH1) v).symm


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
