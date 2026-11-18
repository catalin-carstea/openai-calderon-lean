import Proof.WeakEnergyAffineTaylor
import Proof.BilinearRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Matrix
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse

/-- Local coefficient entries control the actual full energy and its
    zero-boundary test restriction. -/
theorem norm_nativeWeakEnergyL_of_entries {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (P : ℝ) (hP : 0 ≤ P) (hA : ∀ x ∈ (ballOpens:Set X),∀ i j,|a x i j| ≤ P) :
    ‖TauCeti.PDE.energyFormH1L ha‖ ≤ 9*P ∧ ‖nativeCoefficientWeakEnergyL a 0 0 ha‖ ≤ 9*P := by
  have hDot (x : X) (hx : x ∈ (ballOpens:Set X)) (eta xi : X) :
      |eta.ofLp ⬝ᵥ (a x *ᵥ xi.ofLp)| ≤ (9*P)*‖eta‖*‖xi‖ :=
    abs_dotProduct_mulVec_le_of_entry_bound (a x) P (hA x hx) eta xi
  have h := TauCeti.PDE.norm_energyFormH1L_le_of_bounds (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ))
    (Lam:=9*P) (beta:=0) (gamma:=0)
    ha (by positivity) hDot le_rfl le_rfl (fun _ _ => by simp) (fun _ _ => by simp)
  have hFull : ‖TauCeti.PDE.energyFormH1L ha‖ ≤ 9*P := by simpa only [add_zero] using h
  refine ⟨hFull,?_⟩
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  rw [nativeCoefficientWeakEnergyL_apply]
  have hn := TauCeti.PDE.norm_energyFormH1_le_of_bounds (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ))
    (Lam:=9*P) (beta:=0) (gamma:=0) (by positivity) hDot le_rfl le_rfl
    (fun _ _ => by simp) (fun _ _ => by simp) u (v:BallH1)
  change ‖TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) u (v:BallH1)‖ ≤ _
  exact hn.trans_eq (by
    change (9*P+0+0)*(‖u‖*‖v‖) = 9*P*‖u‖*‖v‖
    ring)

end ShrinkingSpheres
