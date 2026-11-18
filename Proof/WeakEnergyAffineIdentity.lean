import Proof.WeakEnergyAffineCross

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
attribute [local irreducible] nativeCoefficientWeakEnergyL

/-- Exact affine coefficient agreement on the physical ball gives exact
    affine agreement of the full native energy forms. -/
theorem fullWeakEnergy_affine_eq {a a0 a1 : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r : ℝ) (hCoeff : ∀ z ∈ (ballOpens:Set X),a z = a0 z+r • a1 z) :
    TauCeti.PDE.energyFormH1L ha = TauCeti.PDE.energyFormH1L ha0+r • TauCeti.PDE.energyFormH1L ha1 := by
  have hN := norm_unitBall_full_energy_affine_remainder_le ha ha0 ha1 r 0 le_rfl (by
    intro z hz i j
    rw [hCoeff z hz]
    have h : a0 z+r • a1 z-a0 z-r • a1 z = 0 := by module
    rw [h]
    simp)
  have hZero : TauCeti.PDE.energyFormH1L ha-TauCeti.PDE.energyFormH1L ha0-r • TauCeti.PDE.energyFormH1L ha1 = 0 :=
    norm_le_zero_iff.mp (by simpa only [mul_zero] using hN)
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hZero)).trans (add_comm _ _)

/-- The same exact local affine identity holds for the actual weak energy
    tested against zero-boundary functions. -/
theorem nativeWeakEnergy_affine_eq {a a0 a1 : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r : ℝ) (hCoeff : ∀ z ∈ (ballOpens:Set X),a z = a0 z+r • a1 z) :
    nativeCoefficientWeakEnergyL a 0 0 ha =
      nativeCoefficientWeakEnergyL a0 0 0 ha0+r • nativeCoefficientWeakEnergyL a1 0 0 ha1 := by
  have hN := norm_nativeWeakEnergy_affine_remainder_le ha ha0 ha1 r 0 le_rfl (by
    intro z hz i j
    rw [hCoeff z hz]
    have h : a0 z+r • a1 z-a0 z-r • a1 z = 0 := by module
    rw [h]
    simp)
  have hZero : nativeCoefficientWeakEnergyL a 0 0 ha-nativeCoefficientWeakEnergyL a0 0 0 ha0-
      r • nativeCoefficientWeakEnergyL a1 0 0 ha1 = 0 :=
    norm_le_zero_iff.mp (by simpa only [mul_zero] using hN)
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hZero)).trans (add_comm _ _)

end ShrinkingSpheres
