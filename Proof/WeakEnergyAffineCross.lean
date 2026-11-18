import Proof.WeakEnergyAffineTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL

/-- The affine full-energy bound also controls the actual weak operator tested
    against zero-boundary functions, by scalar evaluation. -/
theorem norm_nativeWeakEnergy_affine_remainder_le {a a0 a1 : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a1 x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ x ∈ (ballOpens:Set X),∀ i j,|(a x-a0 x-r • a1 x) i j| ≤ q) :
    ‖nativeCoefficientWeakEnergyL a 0 0 ha-nativeCoefficientWeakEnergyL a0 0 0 ha0-
      r • nativeCoefficientWeakEnergyL a1 0 0 ha1‖ ≤ 9*q := by
  let E := TauCeti.PDE.energyFormH1L ha-TauCeti.PDE.energyFormH1L ha0-
    r • TauCeti.PDE.energyFormH1L ha1
  have hE : ‖E‖ ≤ 9*q :=
    norm_unitBall_full_energy_affine_remainder_le (a:=a) (a0:=a0) (a1:=a1) ha ha0 ha1 r q hq hDiff
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hPoint : (nativeCoefficientWeakEnergyL a 0 0 ha-nativeCoefficientWeakEnergyL a0 0 0 ha0-
      r • nativeCoefficientWeakEnergyL a1 0 0 ha1) u v = E u (v:BallH1) := by
    change nativeCoefficientWeakEnergyL a 0 0 ha u v-nativeCoefficientWeakEnergyL a0 0 0 ha0 u v-
      r*nativeCoefficientWeakEnergyL a1 0 0 ha1 u v = _
    rw [nativeCoefficientWeakEnergyL_apply a 0 0 ha u v,
      nativeCoefficientWeakEnergyL_apply a0 0 0 ha0 u v,
      nativeCoefficientWeakEnergyL_apply a1 0 0 ha1 u v]
    dsimp only [E]
    simp only [_root_.sub_apply,_root_.smul_apply,smul_eq_mul,
      TauCeti.PDE.energyFormH1L_apply]
    rfl
  rw [hPoint]
  exact (E.le_opNorm₂ u (v:BallH1)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (norm_nonneg _)) (norm_nonneg _))

end ShrinkingSpheres
