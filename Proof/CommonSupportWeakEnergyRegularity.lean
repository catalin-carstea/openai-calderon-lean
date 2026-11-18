import Proof.CommonSupportPoissonRegularity
import Proof.Archive.NativeSmoothCoefficientFullEnergy
import Proof.Archive.NativeFullFiniteForcingTopology
import Proof.Archive.NativeContinuousCoefficientOrthogonalEnergy
import Proof.Archive.NativeCoefficientWeakConormalEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem commonSupportEnergyMemLp (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    MemLp (fun z => TauCeti.PDE.energyIntegrand (a (p,z)) (0:X) (0:ℝ)) ⊤
      ((volume : Measure X).restrict ballOpens) :=
  memLp_nativeEnergyIntegrand_of_continuous (fun z => a (p,z)) (fun _ => 0) (fun _ => 0)
    (ha.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const continuous_const

def commonSupportFullWeakEnergy (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=fun z => a (p,z)) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) (commonSupportEnergyMemLp a ha p)

def commonSupportWeakEnergy (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeCoefficientWeakEnergyL (fun z => a (p,z)) (fun _ => (0:X)) (fun _ => (0:ℝ))
    (commonSupportEnergyMemLp a ha p)

def commonSupportZeroWeakEnergy (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeZeroCoefficientEnergyL (fun z => a (p,z)) (fun _ => (0:X)) (fun _ => (0:ℝ))
    (commonSupportEnergyMemLp a ha p)

lemma commonSupportFullWeakEnergy_smooth_eq
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) :
    nativeSmoothCoefficientFullEnergyL fixedSobolevCalculus
      (commonSupportMatrixFamily 1 a ha S hS hz p) (fun _ => 0) = commonSupportFullWeakEnergy a ha p := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [nativeSmoothCoefficientFullEnergyL_apply]
  change _ = TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=fun z => a (p,z)) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ))
      (commonSupportEnergyMemLp a ha p) u v
  rw [TauCeti.PDE.energyFormH1L_apply,coefficientMatrixField_commonSupportMatrixFamily]
  have hDrift : nativeSmoothDriftField (fun _ => (0:SmoothCoefficientJets 1)) = (fun _ => (0:X)) := by
    funext z
    ext i
    rfl
  rw [hDrift]
  rfl

/-- Smooth genuine weak energy forms from a common-support matrix family. -/
theorem contDiff_commonSupportFullWeakEnergy
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) : ContDiff ℝ ∞ (commonSupportFullWeakEnergy a ha) := by
  have hNative : ContDiff ℝ ∞ (fun p => nativeSmoothCoefficientFullEnergyL fixedSobolevCalculus
      (commonSupportMatrixFamily 1 a ha S hS hz p) (fun _ => 0)) := by
    unfold nativeSmoothCoefficientFullEnergyL
    exact contDiff_nativeFullFiniteForcingEnergy
      (fun i j p => coefficientMultiplier fixedSobolevCalculus 0 (commonSupportMatrixFamily 1 a ha S hS hz p i j))
      (fun _ _ => coefficientMultiplier fixedSobolevCalculus 0 (0:SmoothCoefficientJets 1))
      (fun i j => contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0
        (fun q => a q i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) S hS
          (fun p z h => by rw [hz p z h];rfl)) (fun _ => contDiff_const)
  have hEq : (fun p => nativeSmoothCoefficientFullEnergyL fixedSobolevCalculus
      (commonSupportMatrixFamily 1 a ha S hS hz p) (fun _ => 0)) = commonSupportFullWeakEnergy a ha :=
    funext (commonSupportFullWeakEnergy_smooth_eq a ha S hS hz)
  rw [hEq] at hNative
  exact hNative

lemma commonSupportWeakEnergy_restriction (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    commonSupportWeakEnergy a ha p =
      ((ContinuousLinearMap.compL ℝ BallH1Zero BallH1 ℝ).flip
        (TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2).toSubmodule.subtypeL).comp
        (commonSupportFullWeakEnergy a ha p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (nativeCoefficientWeakEnergyL_apply _ _ _ _ u v).trans
    (TauCeti.PDE.energyFormH1L_apply (commonSupportEnergyMemLp a ha p) u (v:BallH1)).symm

lemma commonSupportZeroWeakEnergy_restriction (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (p : P) :
    commonSupportZeroWeakEnergy a ha p = (commonSupportWeakEnergy a ha p).comp
      (TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2).toSubmodule.subtypeL := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (nativeZeroCoefficientEnergyL_apply _ _ _ _ u v).trans
    (nativeCoefficientWeakEnergyL_restriction _ _ _ _ u v)

theorem contDiff_commonSupportWeakEnergy
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) : ContDiff ℝ ∞ (commonSupportWeakEnergy a ha) := by
  have hSmooth := contDiff_commonSupportFullWeakEnergy a ha S hS hz
  have hResult : ContDiff ℝ ∞ (fun p =>
      ((ContinuousLinearMap.compL ℝ BallH1Zero BallH1 ℝ).flip
        (TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2).toSubmodule.subtypeL).comp
        (commonSupportFullWeakEnergy a ha p)) := contDiff_const.clm_comp hSmooth
  simpa only [← commonSupportWeakEnergy_restriction] using hResult

theorem contDiff_commonSupportZeroWeakEnergy
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) : ContDiff ℝ ∞ (commonSupportZeroWeakEnergy a ha) := by
  have hSmooth := contDiff_commonSupportWeakEnergy a ha S hS hz
  have hResult : ContDiff ℝ ∞ (fun p => (commonSupportWeakEnergy a ha p).comp
      (TauCeti.w1p0Submodule (volume : Measure X) ballOpens 2).toSubmodule.subtypeL) :=
    hSmooth.clm_comp contDiff_const
  simpa only [← commonSupportZeroWeakEnergy_restriction] using hResult

end ShrinkingSpheres
