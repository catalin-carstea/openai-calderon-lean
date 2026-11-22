module

public import Proof.CalderonN.SmoothSupportedFiberJetCalculus
public import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus

import Mathlib.Tactic

/-! Pair a regular fiber coefficient with its actual angular adjoint.
Reversing products here also determines the adjoints of the
coefficients in the divergence form. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

namespace RegularTraceFiberFamily

@[expose] def neg (F : RegularTraceFiberFamily Y) : RegularTraceFiberFamily Y :=
  ⟨fun y => -F.1 y,F.2.neg⟩

theorem action_neg (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) :
    F.neg.action hY = -F.action hY := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [action_fiber,neg,LinearMap.neg_apply,map_neg]

theorem scalar_comm (hY : IsOpen Y) (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y)
    (F : RegularTraceFiberFamily Y) :
    (scalar hY f hf).action hY*F.action hY = F.action hY*(scalar hY f hf).action hY := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [Module.End.mul_apply,action_fiber,scalar,LinearMap.smul_apply,Module.End.one_apply,map_smul]

end RegularTraceFiberFamily

structure PairedTraceFiberFamily (hn : 3 ≤ dim) (Y : Set (X dim)) where
  forward : RegularTraceFiberFamily Y
  reverse : RegularTraceFiberFamily Y
  pair : ∀ x ∈ Y,SmoothTraceAdjoint hn (forward.1 x) (reverse.1 x)

namespace PairedTraceFiberFamily

variable {hn : 3 ≤ dim}

@[expose] def symmetric (F : RegularTraceFiberFamily Y) (hF : ∀ x ∈ Y,SmoothTraceAdjoint hn (F.1 x) (F.1 x)) :
    PairedTraceFiberFamily hn Y := ⟨F,F,hF⟩

@[expose] def scalar (hY : IsOpen Y) (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    PairedTraceFiberFamily hn Y :=
  symmetric (RegularTraceFiberFamily.scalar hY f hf) (fun x _ u v => by
    simp only [RegularTraceFiberFamily.scalar,LinearMap.smul_apply,Module.End.one_apply,map_smul,
      real_inner_smul_left,real_inner_smul_right])

@[expose] def adj (F : PairedTraceFiberFamily hn Y) : PairedTraceFiberFamily hn Y :=
  ⟨F.reverse,F.forward,fun x hx u v =>
    (real_inner_comm _ _).trans ((F.pair x hx v u).symm.trans (real_inner_comm _ _))⟩

@[expose] def neg (F : PairedTraceFiberFamily hn Y) : PairedTraceFiberFamily hn Y :=
  ⟨F.forward.neg,F.reverse.neg,fun x hx u v => by
    simpa only [RegularTraceFiberFamily.neg,LinearMap.neg_apply,map_neg,inner_neg_left,inner_neg_right] using
      congrArg Neg.neg (F.pair x hx u v)⟩

@[expose] def add (F G : PairedTraceFiberFamily hn Y) : PairedTraceFiberFamily hn Y :=
  ⟨F.forward.add G.forward,F.reverse.add G.reverse,fun x hx => (F.pair x hx).add (G.pair x hx)⟩

@[expose] def sub (F G : PairedTraceFiberFamily hn Y) : PairedTraceFiberFamily hn Y :=
  ⟨F.forward.sub G.forward,F.reverse.sub G.reverse,fun x hx => (F.pair x hx).sub (G.pair x hx)⟩

@[expose] def mul (hY : IsOpen Y) (F G : PairedTraceFiberFamily hn Y) : PairedTraceFiberFamily hn Y :=
  ⟨F.forward.mul hY G.forward,G.reverse.mul hY F.reverse,fun x hx => (F.pair x hx).mul (G.pair x hx)⟩

@[expose] def derivative (hY : IsOpen Y) (a : X dim) (F : PairedTraceFiberFamily hn Y) :
    PairedTraceFiberFamily hn Y :=
  ⟨F.forward.derivative hY a,F.reverse.derivative hY a,fun x hx =>
    F.forward.iteratedDerivative_paired hn hY F.reverse F.pair 1 (fun _ => a) hx⟩

@[expose] def finiteSum {ι : Type*} (s : Finset ι) (F : ι → PairedTraceFiberFamily hn Y) :
    PairedTraceFiberFamily hn Y :=
  ⟨RegularTraceFiberFamily.finiteSum s (fun i => (F i).forward),
    RegularTraceFiberFamily.finiteSum s (fun i => (F i).reverse),
    fun x hx u v => by
      simp only [RegularTraceFiberFamily.finiteSum,LinearMap.sum_apply,map_sum,sum_inner,inner_sum]
      exact Finset.sum_congr rfl (fun i _ => (F i).pair x hx u v)⟩

theorem pairedAction (F : PairedTraceFiberFamily hn Y) (hY : IsOpen Y)
    (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) (F.forward.action hY) (F.reverse.action hY) :=
  pairedAdjoint_supportedFiber hn hY μ hμ F.forward.1 F.reverse.1 F.forward.2 F.reverse.2 F.pair

end PairedTraceFiberFamily

end CalderonN
