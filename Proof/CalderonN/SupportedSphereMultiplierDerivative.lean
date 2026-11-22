module

public import Proof.CalderonN.SupportedSphereMultiplierFamily
public import Proof.CalderonN.SmoothSupportedFiberMatrixDerivative

import Mathlib.Tactic

/-! Identify the derivative of a smooth multiplier using its local
scalar representative on a neighborhood of the physical fiber. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 3100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq (hY : IsOpen Y)
    {F G : X dim → Module.End ℝ (SmoothSphereTrace dim)}
    (hF : SmoothSupportedTraceFiberRegular Y F) (hG : SmoothSupportedTraceFiberRegular Y G)
    (a : X dim) {x : X dim} (hx : x ∈ Y) (h : F =ᶠ[𝓝 x] G) :
    smoothSupportedTraceFiberDerivative hY F hF a x = smoothSupportedTraceFiberDerivative hY G hG a x := by
  ext u : 1
  obtain ⟨s,rfl⟩ := smoothSupportedTraceFiberL_surjective_of_mem hY hx u
  rw [smoothSupportedTraceFiberDerivative_apply hY F hF a hx,
    smoothSupportedTraceFiberDerivative_apply hY G hG a hx]
  let A := smoothSupportedTraceFiberAction hY F hF
  let B := smoothSupportedTraceFiberAction hY G hG
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  have hAB : (fun y => smoothSupportedTraceFiberL y (A s)) =ᶠ[𝓝 x]
      (fun y => smoothSupportedTraceFiberL y (B s)) := by
    filter_upwards [h,hY.mem_nhds hx] with y hy hyY
    simp only [A,B,smoothSupportedTraceFiberAction_fiber,hy]
  have hD := smoothSupportedTraceFiberL_baseDiff_congr_nhds a hAB
  have hZ : smoothSupportedTraceFiberL x (A (D s)) = smoothSupportedTraceFiberL x (B (D s)) := by
    simp only [A,B,smoothSupportedTraceFiberAction_fiber,h.eq_of_nhds]
  change smoothSupportedTraceFiberL x ((D*A-A*D) s) = smoothSupportedTraceFiberL x ((D*B-B*D) s)
  simp only [LinearMap.sub_apply,map_sub,Module.End.mul_apply,hZ]
  exact congrArg (fun v => v-smoothSupportedTraceFiberL x (B (D s))) hD

theorem smoothSupportedTraceFiberDerivative_const (hY : IsOpen Y)
    (T : Module.End ℝ (SmoothSphereTrace dim))
    (hT : SmoothSupportedTraceFiberRegular Y (fun _ => T)) (a : X dim) {x : X dim} (hx : x ∈ Y) :
    smoothSupportedTraceFiberDerivative hY (fun _ => T) hT a x = 0 := by
  ext u : 1
  obtain ⟨s,hs⟩ := exists_supportedTrace_const_fiber_near hY hx u
  let A := smoothSupportedTraceFiberAction hY (fun _ => T) hT
  have hsA : ∀ᶠ y in 𝓝 x,smoothSupportedTraceFiberL y (A s) = T u := by
    filter_upwards [hs,hY.mem_nhds hx] with y hy hyY
    simp only [A,smoothSupportedTraceFiberAction_fiber,hy]
  rw [← hs.self_of_nhds,smoothSupportedTraceFiberDerivative_apply hY _ hT a hx]
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  change smoothSupportedTraceFiberL x ((D*A-A*D) s) = 0
  simp only [LinearMap.sub_apply,map_sub,Module.End.mul_apply,A,D,
    smoothSupportedTraceFiberL_baseDiff_eq_zero_of_locally_const a hsA,
    smoothSupportedTraceFiberAction_fiber,
    smoothSupportedTraceFiberL_baseDiff_eq_zero_of_locally_const a hs,map_zero,sub_zero,LinearMap.zero_apply]

theorem supportedSphereMultiplierFamily_derivative_eq (hY : IsOpen Y)
    (m : ∀ x ∈ Y,SmoothData dim)
    (hF : SmoothSupportedTraceFiberRegular Y (supportedSphereMultiplierFamily m))
    {x : X dim} (hx : x ∈ Y) (a : X dim) (p : X dim × X dim → ℝ)
    (hp : ∀ z ∈ standardSphere dim,ContDiffAt ℝ ∞ p (x,z))
    (hRep : ∀ z ∈ standardSphere dim, ∀ᶠ y in 𝓝 x,
      ∀ hy : y ∈ Y,p (y,z) = (m y hy).1 z)
    (g : SmoothData dim)
    (hDeriv : ∀ z ∈ standardSphere dim, (fderiv ℝ (fun y => p (y,z)) x) a = g.1 z) :
    smoothSupportedTraceFiberDerivative hY (supportedSphereMultiplierFamily m) hF a x =
      smoothSphereTraceMul g := by
  ext u : 1
  obtain ⟨s,hs⟩ := exists_supportedTrace_const_fiber_near hY hx u
  let F := supportedSphereMultiplierFamily m
  let A := smoothSupportedTraceFiberAction hY F hF
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  have hD : smoothSupportedTraceFiberL x (D s) = 0 :=
    smoothSupportedTraceFiberL_baseDiff_eq_zero_of_locally_const a hs
  rw [← hs.self_of_nhds,smoothSupportedTraceFiberDerivative_apply hY F hF a hx,hs.self_of_nhds]
  change smoothSupportedTraceFiberL x ((D*A-A*D) s) = smoothSphereTraceMul g u
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,A,
    smoothSupportedTraceFiberAction_fiber,hD,map_zero,sub_zero]
  apply Subtype.ext
  funext z
  have hEq : (fun y => (A s).1 (y,z)) =ᶠ[𝓝 x] fun y => p (y,z)*u.1 z := by
    filter_upwards [hs,hY.mem_nhds hx,hRep z.1 z.2] with y hy hY' hP
    change (smoothSupportedTraceFiberL y (A s)).1 z = _
    simp only [A,F,smoothSupportedTraceFiberAction_fiber,hy,supportedSphereMultiplierFamily,
      dite_eq_left hY',smoothSphereTraceMul_apply,hP hY']
  have hDiff : DifferentiableAt ℝ (fun y => p (y,z)) x :=
    ((hp z.1 z.2).comp x (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  simp only [smoothSupportedTraceFiberL_apply,D,smoothSupportedTraceBaseDiff_apply,standardTraceBaseDiff,
    smoothSphereTraceMul_apply]
  change fderiv ℝ (fun y => (A s).1 (y,z)) x a = g.1 z*u.1 z
  rw [hEq.fderiv_eq]
  rw [show (fun y => p (y,z)*u.1 z) = (u.1 z) • (fun y => p (y,z)) by ext y; simp [mul_comm],
    fderiv_const_smul hDiff,ContinuousLinearMap.smul_apply,hDeriv z.1 z.2]
  exact mul_comm _ _

end CalderonN
