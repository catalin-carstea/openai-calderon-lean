module

public import Proof.CalderonN.SmoothSupportedFiberDerivative

import Proof.CalderonN.SmoothSupportedTraceBaseCommutation
import Proof.CalderonN.SmoothTraceAngularCommutator
import Mathlib.Tactic

/-! Base coefficient differentiation obeys the sum and product rules
on the common smooth trace core. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

private theorem operator_comm_sub_right {R : Type*} [Ring R] (A B C : R) :
    A*(B-C)-(B-C)*A = (A*B-B*A)-(A*C-C*A) := by noncomm_ring

section
variable (hY : IsOpen Y) (F G : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (hG : SmoothSupportedTraceFiberRegular Y G)

theorem smoothSupportedTraceFiberAction_mul :
    smoothSupportedTraceFiberAction hY (fun x => F x*G x) (hF.mul hY hG) =
      smoothSupportedTraceFiberAction hY F hF*smoothSupportedTraceFiberAction hY G hG := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [smoothSupportedTraceFiberAction_fiber,Module.End.mul_apply]

theorem smoothSupportedTraceFiberAction_add :
    smoothSupportedTraceFiberAction hY (fun x => F x+G x) (hF.add hG) =
      smoothSupportedTraceFiberAction hY F hF+smoothSupportedTraceFiberAction hY G hG := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [smoothSupportedTraceFiberAction_fiber,LinearMap.add_apply,map_add]

theorem smoothSupportedTraceFiberDerivative_mul (a : X dim) {x : X dim} (hx : x ∈ Y) :
    smoothSupportedTraceFiberDerivative hY (fun x => F x*G x) (hF.mul hY hG) a x =
      smoothSupportedTraceFiberDerivative hY F hF a x*G x+
        F x*smoothSupportedTraceFiberDerivative hY G hG a x := by
  let A := smoothSupportedTraceFiberAction hY F hF
  let B := smoothSupportedTraceFiberAction hY G hG
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  ext u : 1
  obtain ⟨v,rfl⟩ := smoothSupportedTraceFiberL_surjective_of_mem hY hx u
  rw [smoothSupportedTraceFiberDerivative_apply hY _ _ a hx v,smoothSupportedTraceFiberAction_mul]
  have h : D*(A*B)-(A*B)*D = (D*A-A*D)*B+A*(D*B-B*D) :=
    operator_comm_mul_right D A B
  change smoothSupportedTraceFiberL x ((D*(A*B)-(A*B)*D) v) = _
  rw [h]
  simp only [LinearMap.add_apply,Module.End.mul_apply,map_add,A,B,D,
    ← smoothSupportedTraceFiberAction_fiber hY G hG v x,
    smoothSupportedTraceFiberDerivative_apply hY F hF a hx,
    ← smoothSupportedTraceFiberAction_fiber hY F hF,
    smoothSupportedTraceFiberDerivative_apply hY G hG a hx]

theorem smoothSupportedTraceFiberDerivative_add (a : X dim) {x : X dim} (hx : x ∈ Y) :
    smoothSupportedTraceFiberDerivative hY (fun x => F x+G x) (hF.add hG) a x =
      smoothSupportedTraceFiberDerivative hY F hF a x+smoothSupportedTraceFiberDerivative hY G hG a x := by
  let A := smoothSupportedTraceFiberAction hY F hF
  let B := smoothSupportedTraceFiberAction hY G hG
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  ext u : 1
  obtain ⟨v,rfl⟩ := smoothSupportedTraceFiberL_surjective_of_mem hY hx u
  rw [smoothSupportedTraceFiberDerivative_apply hY _ _ a hx v,smoothSupportedTraceFiberAction_add]
  have h : D*(A+B)-(A+B)*D = (D*A-A*D)+(D*B-B*D) := by noncomm_ring
  change smoothSupportedTraceFiberL x ((D*(A+B)-(A+B)*D) v) = _
  rw [h]
  simp only [LinearMap.add_apply,map_add,smoothSupportedTraceFiberDerivative_apply hY _ _ a hx]
  rfl

theorem smoothSupportedTraceFiberDerivative_sub (a : X dim) {x : X dim} (hx : x ∈ Y) :
    smoothSupportedTraceFiberDerivative hY (fun x => F x-G x) (hF.sub hG) a x =
      smoothSupportedTraceFiberDerivative hY F hF a x-smoothSupportedTraceFiberDerivative hY G hG a x := by
  let A := smoothSupportedTraceFiberAction hY F hF
  let B := smoothSupportedTraceFiberAction hY G hG
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  have hEq : smoothSupportedTraceFiberAction hY (fun x => F x-G x) (hF.sub hG) = A-B := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x _
    simp only [A,B,smoothSupportedTraceFiberAction_fiber,LinearMap.sub_apply,map_sub]
  ext u : 1
  obtain ⟨v,rfl⟩ := smoothSupportedTraceFiberL_surjective_of_mem hY hx u
  rw [smoothSupportedTraceFiberDerivative_apply hY _ _ a hx v,hEq]
  have h : D*(A-B)-(A-B)*D = (D*A-A*D)-(D*B-B*D) :=
    operator_comm_sub_right D A B
  change smoothSupportedTraceFiberL x ((D*(A-B)-(A-B)*D) v) = _
  rw [h]
  simp only [LinearMap.sub_apply,map_sub,smoothSupportedTraceFiberDerivative_apply hY _ _ a hx]
  rfl

end

theorem smoothSupportedTraceFiberDerivative_scalar (hY : IsOpen Y)
    (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) (a : X dim) {x : X dim} (hx : x ∈ Y) :
    smoothSupportedTraceFiberDerivative hY (fun x => f x • (1 : Module.End ℝ (SmoothSphereTrace dim)))
      (smoothSupportedTraceFiberRegular_smul hY hf) a x =
      fderiv ℝ f x a • (1 : Module.End ℝ (SmoothSphereTrace dim)) := by
  have hEq : smoothSupportedTraceFiberAction hY _ (smoothSupportedTraceFiberRegular_smul hY hf) =
      smoothSupportedTraceBaseMul hY f hf := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x _
    simp only [smoothSupportedTraceFiberAction_fiber,smoothSupportedTraceBaseMul_fiber,
      LinearMap.smul_apply,Module.End.one_apply]
  ext u : 1
  obtain ⟨v,rfl⟩ := smoothSupportedTraceFiberL_surjective_of_mem hY hx u
  rw [smoothSupportedTraceFiberDerivative_apply hY _ _ a hx v,hEq]
  have h := smoothSupportedTraceBaseDiff_mul hY a f hf
  have hCancel : smoothSupportedTraceBaseDiff (Y:=Y) a*smoothSupportedTraceBaseMul hY f hf-
      smoothSupportedTraceBaseMul hY f hf*smoothSupportedTraceBaseDiff a =
      smoothSupportedTraceBaseMul hY (fun x => fderiv ℝ f x a)
        ((hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const) := by
    rw [h]
    abel
  rw [hCancel]
  simp only [smoothSupportedTraceBaseMul_fiber,LinearMap.smul_apply,Module.End.one_apply]

end CalderonN
