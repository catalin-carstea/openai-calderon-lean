import Proof.WeakEnergyAffineCross
import Proof.NativeWeakTaylorOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeZeroCoefficientEnergyL nativeCoefficientWeakEnergyL

lemma nativeZeroFullEnergy_eval (a : X → Mat)
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (u v : BallH1Zero) :
    nativeZeroCoefficientEnergyL a 0 0 ha u v = TauCeti.PDE.energyFormH1L ha (u:BallH1) (v:BallH1) := by
  have h1 := nativeZeroCoefficientEnergyL_apply a (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) ha u v
  have h2 := nativeCoefficientWeakEnergyL_restriction a (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) ha u v
  have h3 := nativeCoefficientWeakEnergyL_apply a (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) ha (u:BallH1) v
  have h4 := TauCeti.PDE.energyFormH1L_apply ha (u:BallH1) (v:BallH1)
  exact h1.trans (h2.trans (h3.trans h4.symm))

/-- The full affine energy estimate restricts to the actual zero-boundary
    energy map by scalar evaluation, preserving the canonical norms. -/
theorem norm_nativeZeroCoefficientEnergy_affine_remainder_le {a a0 a1 : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ x ∈ (ballOpens:Set X),∀ i j,|(a x-a0 x-r • a1 x) i j| ≤ q) :
    ‖nativeZeroCoefficientEnergyL a 0 0 ha-nativeZeroCoefficientEnergyL a0 0 0 ha0-
      r • nativeZeroCoefficientEnergyL a1 0 0 ha1‖ ≤ 9*q := by
  let E : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
    TauCeti.PDE.energyFormH1L (a:=a) (b:=fun _ : X => (0:X)) (c:=fun _ : X => (0:ℝ)) ha-
    TauCeti.PDE.energyFormH1L (a:=a0) (b:=fun _ : X => (0:X)) (c:=fun _ : X => (0:ℝ)) ha0-
    r • TauCeti.PDE.energyFormH1L (a:=a1) (b:=fun _ : X => (0:X)) (c:=fun _ : X => (0:ℝ)) ha1
  have hE : ‖E‖ ≤ 9*q :=
    norm_unitBall_full_energy_affine_remainder_le (a:=a) (a0:=a0) (a1:=a1) ha ha0 ha1 r q hq hDiff
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hPoint : (nativeZeroCoefficientEnergyL a 0 0 ha-nativeZeroCoefficientEnergyL a0 0 0 ha0-
      r • nativeZeroCoefficientEnergyL a1 0 0 ha1) u v = E (u:BallH1) (v:BallH1) := by
    change nativeZeroCoefficientEnergyL a 0 0 ha u v-nativeZeroCoefficientEnergyL a0 0 0 ha0 u v-
      r*nativeZeroCoefficientEnergyL a1 0 0 ha1 u v = _
    have h1 := nativeZeroFullEnergy_eval a ha u v
    have h2 := nativeZeroFullEnergy_eval a0 ha0 u v
    have h3 := nativeZeroFullEnergy_eval a1 ha1 u v
    have h12 := congrArg₂ (fun x y : ℝ => x-y) h1 h2
    have hScalar := congrArg₂ (fun x z : ℝ => x-r*z) h12 h3
    exact hScalar

  rw [hPoint]
  exact (E.le_opNorm₂ (u:BallH1) (v:BallH1)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (norm_nonneg _)) (norm_nonneg _))

end ShrinkingSpheres
