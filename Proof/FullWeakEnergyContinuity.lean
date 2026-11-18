import Proof.WeakDirichletContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open Set MeasureTheory Matrix
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Coefficient entry control bounds the actual weak energy operator difference. -/
theorem norm_unitBall_full_energyForm_sub_le
    {a a0 : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (hcoeff0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|a x i j-a0 x i j| ≤ q) :
    ‖TauCeti.PDE.energyFormH1L hcoeff-TauCeti.PDE.energyFormH1L hcoeff0‖ ≤ 9*q := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hSub : TauCeti.PDE.energyFormH1 (fun x => a x-a0 x) (fun _ => (0:X)) (fun _ => (0:ℝ)) u v =
      TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) u v-
      TauCeti.PDE.energyFormH1 a0 (fun _ => (0:X)) (fun _ => (0:ℝ)) u v := by
    have hh := TauCeti.PDE.energyFormIntegral_sub
      ((volume:Measure X).restrict ballOpens) a (fun _ => (0:X)) (fun _ => (0:ℝ))
      (TauCeti.PDE.jetField u) (TauCeti.PDE.jetField v)
      a0 (fun _ => (0:X)) (fun _ => (0:ℝ))
      (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u v)
      (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff0 u v)
    simpa only [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormIntegral_def,sub_zero] using hh
  change ‖TauCeti.PDE.energyFormH1L hcoeff u v-TauCeti.PDE.energyFormH1L hcoeff0 u v‖ ≤ _
  rw [TauCeti.PDE.energyFormH1L_apply,TauCeti.PDE.energyFormH1L_apply,← hSub]
  have hDot (x : X) (hx : x ∈ (ballOpens : Set X)) (eta xi : X) :
      |eta.ofLp ⬝ᵥ ((a x-a0 x) *ᵥ xi.ofLp)| ≤ (9*q)*‖eta‖*‖xi‖ :=
    abs_dotProduct_mulVec_le_of_entry_bound (a x-a0 x) q (fun i j => hDiff x hx i j) eta xi
  have hn := TauCeti.PDE.norm_energyFormH1_le_of_bounds (a:=fun x => a x-a0 x)
    (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) (Lam:=9*q) (beta:=0) (gamma:=0)
    (show 0 ≤ 9*q by positivity) hDot le_rfl le_rfl (fun _ _ => by simp) (fun _ _ => by simp)
    u v
  simpa only [add_zero,mul_assoc] using hn

end ShrinkingSpheres
