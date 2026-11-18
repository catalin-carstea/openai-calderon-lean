import Proof.EndpointBoundaryCalculus
import Proof.FullCoefficientEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- The constructive value-trace kernel and coercivity give uniqueness among
    all H1 harmonic solutions with the same native boundary trace. -/
theorem weak_harmonic_eq_of_valueTrace_eq {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (U V : BallH1)
    (hU : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) U (v : BallH1) = 0)
    (hV : ∀ v : BallH1Zero,TauCeti.PDE.energyFormH1 a (fun _ => (0:X)) (fun _ => (0:ℝ)) V (v : BallH1) = 0)
    (hTrace : fixedUnitBallValueTrace.valueTraceL U = fixedUnitBallValueTrace.valueTraceL V) : U = V := by
  have hMem : U-V ∈ TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2 := by
    apply (fixedUnitBallValueTrace_kernel (U-V)).1
    rw [map_sub,hTrace,sub_self]
  let w : BallH1Zero := ⟨U-V,hMem⟩
  let B := TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X)) (Omega:=ballOpens)
    (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff
  have hUU : TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff U (w : BallH1) = 0 := by
    rw [TauCeti.PDE.energyFormH1L_apply]
    exact hU w
  have hVV : TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff V (w : BallH1) = 0 := by
    rw [TauCeti.PDE.energyFormH1L_apply]
    exact hV w
  have hww : B w w = 0 := by
    change TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff (U-V) (w : BallH1) = 0
    rw [(TauCeti.PDE.energyFormH1L (mu:=(volume:Measure X)) (Omega:=ballOpens)
      (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff).map_sub U V,
      _root_.sub_apply,hUU,hVV,sub_self]
  obtain ⟨α,hα,hCoerce⟩ := hc
  have hNorm : ‖w‖ = 0 := by
    by_contra hn
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr (fun hz => hn (by rw [hz,norm_zero]))
    have hlt : 0 < α*‖w‖*‖w‖ := mul_pos (mul_pos hα hpos) hpos
    have hb := hCoerce w
    rw [hww] at hb
    exact (not_lt_of_ge hb) hlt
  have hw : w = 0 := norm_eq_zero.mp hNorm
  have hVal := congrArg (fun z : BallH1Zero => (z : BallH1)) hw
  exact sub_eq_zero.mp hVal

end ShrinkingSpheres
