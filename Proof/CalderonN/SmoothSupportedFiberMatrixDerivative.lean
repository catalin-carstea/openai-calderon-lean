module

public import Proof.CalderonN.SmoothSupportedFiberDerivative
public import Proof.CalderonN.SmoothSupportedTraceAdjoints

import Proof.CalderonN.SmoothTraceLinearAdjunction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Ordinary differentiation of the supported fiber pairing gives
the matrix element of the actual base-commutator operator. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff InnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceFiberL_baseDiff_eq_zero_of_locally_const
    (a : X dim) {x : X dim} {s : SmoothSupportedTraceSection Y} {u : SmoothSphereTrace dim}
    (h : ∀ᶠ y in 𝓝 x,smoothSupportedTraceFiberL y s = u) :
    smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff a s) = 0 := by
  apply Subtype.ext
  funext z
  have hEq : (fun y => s.1 (y,z)) =ᶠ[𝓝 x] (fun _ => u.1 z) := by
    filter_upwards [h] with y hy
    exact congrArg (fun w : SmoothSphereTrace dim => w.1 z) hy
  simp only [smoothSupportedTraceFiberL_apply,smoothSupportedTraceBaseDiff_apply,standardTraceBaseDiff,
    Submodule.coe_zero,Pi.zero_apply,hEq.fderiv_eq,fderiv_fun_const,zero_apply]

theorem contDiffAt_smoothTrace_fiber_matrix_element (hn : 3 ≤ dim)
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    (u v : SmoothSphereTrace dim) :
    ContDiffAt ℝ ∞ (fun y => ⟪smoothSphereTraceL2 hn (F y u),smoothSphereTraceL2 hn v⟫_ℝ) x := by
  let A := smoothSupportedTraceFiberAction hY F hF
  let L := smoothSphereTraceL2 hn
  obtain ⟨s,hs⟩ := exists_supportedTrace_const_fiber_near hY hx u
  have hEq : (fun y => ⟪smoothSupportedTraceL2 hn (A s) y,L v⟫_ℝ) =ᶠ[𝓝 x]
      (fun y => ⟪L (F y u),L v⟫_ℝ) := by
    filter_upwards [hs,hY.mem_nhds hx] with y hy hyY
    rw [smoothSupportedTraceL2,show A = _ from rfl,smoothSupportedTraceFiberAction_fiber,hy]
  exact (((contDiff_smoothSupportedTraceL2 hn (A s)).inner ℝ contDiff_const).contDiffAt).congr_of_eventuallyEq
    hEq.symm

theorem fderiv_smoothTrace_fiber_matrix_element (hn : 3 ≤ dim)
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    (a : X dim) (u v : SmoothSphereTrace dim) :
    fderiv ℝ (fun y => ⟪smoothSphereTraceL2 hn (F y u),smoothSphereTraceL2 hn v⟫_ℝ) x a =
      ⟪smoothSphereTraceL2 hn (smoothSupportedTraceFiberDerivative hY F hF a x u),
        smoothSphereTraceL2 hn v⟫_ℝ := by
  let A := smoothSupportedTraceFiberAction hY F hF
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  let L := smoothSphereTraceL2 hn
  obtain ⟨s,hs⟩ := exists_supportedTrace_const_fiber_near hY hx u
  have hEq : (fun y => ⟪smoothSupportedTraceL2 hn (A s) y,L v⟫_ℝ) =ᶠ[𝓝 x]
      (fun y => ⟪L (F y u),L v⟫_ℝ) := by
    filter_upwards [hs,hY.mem_nhds hx] with y hy hyY
    rw [smoothSupportedTraceL2,show A = _ from rfl,smoothSupportedTraceFiberAction_fiber,hy]
  have hDu := smoothSupportedTraceFiberL_baseDiff_eq_zero_of_locally_const a hs
  have hB : smoothSupportedTraceFiberL x ((D*A-A*D) s) =
      smoothSupportedTraceFiberL x (D (A s)) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,A,D,
      smoothSupportedTraceFiberAction_fiber,hDu,map_zero,sub_zero]
  rw [← hEq.fderiv_eq,
    fderiv_inner_apply ℝ ((contDiff_smoothSupportedTraceL2 hn (A s)).differentiable (by simp) x)
      (differentiableAt_const _),
    fderiv_fun_const,Pi.zero_apply,zero_apply,inner_zero_right,zero_add,
    fderiv_smoothSupportedTraceL2,← hs.self_of_nhds,
    smoothSupportedTraceFiberDerivative_apply hY F hF a hx s,hB]
  rfl

theorem smoothSupportedTraceFiberDerivative_symmetric (hn : 3 ≤ dim)
    (hY : IsOpen Y) (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F)
    (hAdj : ∀ x ∈ Y,SmoothTraceAdjoint hn (F x) (F x)) (a : X dim) {x : X dim} (hx : x ∈ Y) :
    SmoothTraceAdjoint hn (smoothSupportedTraceFiberDerivative hY F hF a x)
      (smoothSupportedTraceFiberDerivative hY F hF a x) := by
  intro u v
  have hEq : (fun y => ⟪smoothSphereTraceL2 hn (F y u),smoothSphereTraceL2 hn v⟫_ℝ) =ᶠ[𝓝 x]
      fun y => ⟪smoothSphereTraceL2 hn (F y v),smoothSphereTraceL2 hn u⟫_ℝ := by
    filter_upwards [hY.mem_nhds hx] with y hy
    exact (hAdj y hy u v).trans (real_inner_comm _ _)
  rw [← fderiv_smoothTrace_fiber_matrix_element hn hY hx F hF a u v,
    real_inner_comm,← fderiv_smoothTrace_fiber_matrix_element hn hY hx F hF a v u,hEq.fderiv_eq]

end CalderonN
