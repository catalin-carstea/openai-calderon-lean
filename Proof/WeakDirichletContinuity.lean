import Proof.FunctionalInversePerturbation
import Proof.NormalMetricCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open Set MeasureTheory Matrix
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma abs_dotProduct_mulVec_le_of_entry_bound (A : Mat) (q : ℝ)
    (hA : ∀ i j,|A i j| ≤ q) (u v : X) :
    |u.ofLp ⬝ᵥ (A *ᵥ v.ofLp)| ≤ (9*q)*‖u‖*‖v‖ := by
  have hNorm := metricBilinear_norm_of_entry_bound (fun _ => A) (0:X) q hA
  rw [show u.ofLp ⬝ᵥ (A *ᵥ v.ofLp) = metricPair (fun _ => A) 0 u v from
    dotProduct_mulVec_eq_metricPair (fun _ => A) 0 u v,← metricBilinear_apply]
  calc
    _ ≤ ‖metricBilinear (fun _ => A) 0‖*‖u‖*‖v‖ := by
      simpa only [Real.norm_eq_abs] using ((metricBilinear (fun _ => A) 0 u).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right ((metricBilinear (fun _ => A) 0).le_opNorm u) (norm_nonneg v))
    _ ≤ _ := by gcongr

/-- Coefficient entry control bounds the actual weak energy operator difference. -/
theorem norm_unitBall_energyForm_sub_le
    {a a0 : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (hcoeff0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (q : ℝ) (hq : 0 ≤ q)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|a x i j-a0 x i j| ≤ q) :
    ‖TauCeti.PDE.energyFormH1L0 hcoeff-TauCeti.PDE.energyFormH1L0 hcoeff0‖ ≤ 9*q := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have hSub : TauCeti.PDE.energyFormH1 (fun x => a x-a0 x) (fun _ => (0:X)) (fun _ => (0:ℝ)) (u : BallH1) (v : BallH1) =
      TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) (u : BallH1) (v : BallH1)-
      TauCeti.PDE.energyFormH1 a0 (fun _ => (0:X)) (fun _ => (0:ℝ)) (u : BallH1) (v : BallH1) := by
    have hh := TauCeti.PDE.energyFormIntegral_sub
      ((volume:Measure X).restrict ballOpens) a (fun _ => (0:X)) (fun _ => (0:ℝ))
      (TauCeti.PDE.jetField (u : BallH1)) (TauCeti.PDE.jetField (v : BallH1))
      a0 (fun _ => (0:X)) (fun _ => (0:ℝ))
      (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff (u : BallH1) (v : BallH1))
      (TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff0 (u : BallH1) (v : BallH1))
    simpa only [TauCeti.PDE.energyFormH1_def,TauCeti.PDE.energyFormIntegral_def,sub_zero] using hh
  change ‖TauCeti.PDE.energyFormH1L0 hcoeff u v-TauCeti.PDE.energyFormH1L0 hcoeff0 u v‖ ≤ _
  rw [TauCeti.PDE.energyFormH1L0_apply,TauCeti.PDE.energyFormH1L0_apply,← hSub]
  have hDot (x : X) (hx : x ∈ (ballOpens : Set X)) (eta xi : X) :
      |eta.ofLp ⬝ᵥ ((a x-a0 x) *ᵥ xi.ofLp)| ≤ (9*q)*‖eta‖*‖xi‖ :=
    abs_dotProduct_mulVec_le_of_entry_bound (a x-a0 x) q (fun i j => hDiff x hx i j) eta xi
  have hn := TauCeti.PDE.norm_energyFormH1_le_of_bounds (a:=fun x => a x-a0 x)
    (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) (Lam:=9*q) (beta:=0) (gamma:=0)
    (show 0 ≤ 9*q by positivity) hDot le_rfl le_rfl (fun _ _ => by simp) (fun _ _ => by simp)
    (u : BallH1) (v : BallH1)
  have huNorm : ‖(u : BallH1)‖ = ‖u‖ := rfl
  have hvNorm : ‖(v : BallH1)‖ = ‖v‖ := rfl
  simpa only [add_zero,mul_assoc,huNorm,hvNorm] using hn

/-- Uniform continuity of weak Dirichlet inverses from energy-form continuity. -/
theorem norm_unitBall_functionalInverse_sub_le
    {a a0 : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (hcoeff0 : MemLp (fun x => TauCeti.PDE.energyIntegrand (a0 x) 0 0)
      ⊤ ((volume : Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff))
    (hc0 : IsCoercive (TauCeti.PDE.energyFormH1L0 hcoeff0))
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hInv : ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)‖ ≤ C)
    (hInv0 : ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff0)‖ ≤ C)
    (hDiff : ∀ x ∈ (ballOpens : Set X),∀ i j,|a x i j-a0 x i j| ≤ q) :
    ‖functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff)-
      functionalInverse (TauCeti.PDE.energyFormH1L0 hcoeff0)‖ ≤ 9*C^2*q := by
  have hD := norm_unitBall_energyForm_sub_le hcoeff hcoeff0 q hq hDiff
  have hn := norm_functionalInverse_sub_le _ _ hc hc0
  exact hn.trans (by
    calc
      _ ≤ C*(9*q)*C := by gcongr
      _ = _ := by ring)

end ShrinkingSpheres
