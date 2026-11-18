import Proof.WeakEnergyAffineTaylor
import Proof.CanonicalWeakInvertibility
import Proof.WeakPoissonComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeZeroCoefficientEnergyL nativeCoefficientWeakEnergyL
  nativeCoefficientWeakFunctionalInverse

theorem nativeZeroCoefficientEnergy_eval {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (u v : BallH1Zero) : nativeZeroCoefficientEnergyL a 0 0 ha u v =
      TauCeti.PDE.energyFormH1 a 0 0 (u:BallH1) (v:BallH1) := by
  unfold nativeZeroCoefficientEnergyL TauCeti.PDE.energyFormH1L0
  rw [ContinuousLinearMap.bilinearComp_apply]
  exact TauCeti.PDE.energyFormH1L_apply ha (u:BallH1) (v:BallH1)

/-- The canonical inverse on the native zero-boundary interface is the
    supplied weak functional inverse, with the same coefficient witness. -/
theorem nativeZeroCoefficientEnergy_inverse_eq {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    (nativeZeroCoefficientEnergyL a 0 0 ha).inverse = nativeCoefficientWeakFunctionalInverse a 0 0 ha := by
  unfold nativeCoefficientWeakFunctionalInverse
  exact (nativeZeroFunctionalInverse_eq_inverse _).symm

theorem nativeZeroCoefficientEnergy_isInvertible {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha)) :
    (nativeZeroCoefficientEnergyL a 0 0 ha).IsInvertible :=
  (nativeZeroCoefficientEnergyL_isInvertible_iff a 0 0 ha).mpr (canonicalWeakEnergy_isInvertible ha hc)

/-- Coefficient differences control the native zero-boundary operator without
    changing inherited normed structures in a later resolvent application. -/
theorem norm_nativeZeroCoefficientEnergy_sub_le {a a0 : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ x ∈ (ballOpens:Set X),∀ i j,|a x i j-a0 x i j| ≤ q) :
    ‖nativeZeroCoefficientEnergyL a 0 0 ha-nativeZeroCoefficientEnergyL a0 0 0 ha0‖ ≤ 9*q := by
  let E := TauCeti.PDE.energyFormH1L ha-TauCeti.PDE.energyFormH1L ha0
  have hE : ‖E‖ ≤ 9*q := norm_unitBall_full_energyForm_sub_le (a:=a) (a0:=a0) ha ha0 q hq hDiff
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hPoint : (nativeZeroCoefficientEnergyL a 0 0 ha-nativeZeroCoefficientEnergyL a0 0 0 ha0) u v =
      E (u:BallH1) (v:BallH1) := by
    change nativeZeroCoefficientEnergyL a 0 0 ha u v-nativeZeroCoefficientEnergyL a0 0 0 ha0 u v = _
    rw [nativeZeroCoefficientEnergy_eval ha u v,nativeZeroCoefficientEnergy_eval ha0 u v]
    dsimp only [E]
    simp only [_root_.sub_apply,TauCeti.PDE.energyFormH1L_apply]
    rfl
  rw [hPoint]
  exact (E.le_opNorm₂ (u:BallH1) (v:BallH1)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (norm_nonneg _)) (norm_nonneg _))

theorem nativeWeakHalfLift_native_assembly {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    nativeWeakHalfLift a 0 0 ha sphereFischerInner = fixedHarmonicH1LiftL-
      (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
        ((nativeCoefficientWeakFunctionalInverse a 0 0 ha).comp
          ((nativeCoefficientWeakEnergyL a 0 0 ha).comp fixedHarmonicH1LiftL)) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun S : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => S f)
    (nativeWeakHalfLift_eq_affineAssembly a 0 0 ha sphereFischerInner)
  exact h.trans (nativeWeakAffineLiftAssembly_apply
    (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
    (nativeCoefficientWeakFunctionalInverse a 0 0 ha)
    (nativeCoefficientWeakEnergyL a 0 0 ha) fixedHarmonicH1LiftL f)

end ShrinkingSpheres
