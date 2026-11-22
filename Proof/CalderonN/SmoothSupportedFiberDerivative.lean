module

public import Proof.CalderonN.SmoothSupportedChartFactorization
public import Proof.CalderonN.SmoothSupportedTraceFiberAction

import Mathlib.Tactic

/-! The commutator of an ordinary base derivative with a smooth
fiber family is again a smooth fiber family. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Classical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceFiberL_baseDiff_congr_nhds
    (a : X dim) {x : X dim} {u v : SmoothSupportedTraceSection Y}
    (h : (fun y => smoothSupportedTraceFiberL y u) =ᶠ[𝓝 x] fun y => smoothSupportedTraceFiberL y v) :
    smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff a u) =
      smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff a v) := by
  apply Subtype.ext
  funext z
  have hEq : (fun y => u.1 (y,z)) =ᶠ[𝓝 x] fun y => v.1 (y,z) := by
    filter_upwards [h] with y hy
    exact congrArg (fun w : SmoothSphereTrace dim => w.1 z) hy
  simp only [smoothSupportedTraceFiberL_apply,smoothSupportedTraceBaseDiff_apply,standardTraceBaseDiff,hEq.fderiv_eq]

theorem smoothSupportedTraceFiberL_baseDiff_eventuallyEq
    (a : X dim) {x : X dim} {u v : SmoothSupportedTraceSection Y}
    (h : (fun y => smoothSupportedTraceFiberL y u) =ᶠ[𝓝 x] fun y => smoothSupportedTraceFiberL y v) :
    (fun y => smoothSupportedTraceFiberL y (smoothSupportedTraceBaseDiff a u)) =ᶠ[𝓝 x]
      fun y => smoothSupportedTraceFiberL y (smoothSupportedTraceBaseDiff a v) := by
  filter_upwards [h.eventually_nhds] with y hy
  exact smoothSupportedTraceFiberL_baseDiff_congr_nhds a hy

theorem smoothSupportedTraceFiberAction_eventuallyEq
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    {u v : SmoothSupportedTraceSection Y}
    (h : (fun y => smoothSupportedTraceFiberL y u) =ᶠ[𝓝 x] fun y => smoothSupportedTraceFiberL y v) :
    (fun y => smoothSupportedTraceFiberL y (smoothSupportedTraceFiberAction hY F hF u)) =ᶠ[𝓝 x]
      fun y => smoothSupportedTraceFiberL y (smoothSupportedTraceFiberAction hY F hF v) := by
  filter_upwards [h,hY.mem_nhds hx] with y hy hyY
  rw [smoothSupportedTraceFiberAction_fiber,smoothSupportedTraceFiberAction_fiber,hy]

theorem smoothSupportedTrace_baseComm_comm_scalar
    (hY : IsOpen Y) (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (a : X dim)
    (c : X dim → ℝ) (hc : ContDiffOn ℝ ∞ c Y) :
    let D := smoothSupportedTraceBaseDiff (Y:=Y) a
    let A := smoothSupportedTraceFiberAction hY F hF
    let C := smoothSupportedTraceBaseMul hY c hc
    (D*A-A*D)*C = C*(D*A-A*D) := by
  dsimp only
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  let A := smoothSupportedTraceFiberAction hY F hF
  let C := smoothSupportedTraceBaseMul hY c hc
  let c' (x : X dim) := fderiv ℝ c x a
  let hc' : ContDiffOn ℝ ∞ c' Y := (hc.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  let C' := smoothSupportedTraceBaseMul hY c' hc'
  have hD : D*C = C*D+C' := smoothSupportedTraceBaseDiff_mul hY a c hc
  have hA : C*A = A*C := smoothSupportedTraceBaseMul_comm_fiber hY c hc F hF
  have hA' : C'*A = A*C' := smoothSupportedTraceBaseMul_comm_fiber hY c' hc' F hF
  have h₁ : D*A*C = C*D*A+C'*A := by rw [mul_assoc D,← hA,← mul_assoc,hD,add_mul]
  have h₂ : A*D*C = C*A*D+C'*A := by rw [mul_assoc A,hD,mul_add,← mul_assoc,← hA,← hA']
  change (D*A-A*D)*C = C*(D*A-A*D)
  rw [sub_mul,h₁,h₂,mul_sub,← mul_assoc C,← mul_assoc C]
  abel

theorem smoothSupportedTrace_baseComm_ker
    (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y) (a : X dim)
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F) :
    let D := smoothSupportedTraceBaseDiff (Y:=Y) a
    let A := smoothSupportedTraceFiberAction hY F hF
    (smoothSupportedTraceFiberL (Y:=Y) x).ker ≤
      ((smoothSupportedTraceFiberL (Y:=Y) x).comp (D*A-A*D)).ker := by
  dsimp only
  intro u hu
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  let A := smoothSupportedTraceFiberAction hY F hF
  let C := D*A-A*D
  let M (i : I dim) := smoothSupportedTraceBaseMul hY (chartDifference x i)
    (contDiff_chartDifference x i).contDiffOn
  obtain ⟨w,hw⟩ := exists_supportedTrace_chart_factorization hY hx u (LinearMap.mem_ker.mp hu)
  let v := ∑ i : I dim,M i (w i)
  have hEq : (fun y => smoothSupportedTraceFiberL y u) =ᶠ[𝓝 x] fun y => smoothSupportedTraceFiberL y v := hw
  have h₁ := smoothSupportedTraceFiberL_baseDiff_eventuallyEq a
    (smoothSupportedTraceFiberAction_eventuallyEq hY hx F hF hEq)
  have h₂ := smoothSupportedTraceFiberAction_eventuallyEq hY hx F hF
    (smoothSupportedTraceFiberL_baseDiff_eventuallyEq a hEq)
  have hC : smoothSupportedTraceFiberL x (C u) = smoothSupportedTraceFiberL x (C v) := by
    simp only [C,LinearMap.sub_apply,map_sub,Module.End.mul_apply,D,A,h₁.eq_of_nhds,h₂.eq_of_nhds]
  rw [LinearMap.mem_ker]
  change smoothSupportedTraceFiberL x (C u) = 0
  rw [hC,show C v = ∑ i : I dim,M i (C (w i)) from ?_]
  · simp only [map_sum,M,smoothSupportedTraceBaseMul_fiber,chartDifference,sub_self,zero_smul,
      Finset.sum_const_zero]
  unfold v
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := smoothSupportedTrace_baseComm_comm_scalar hY F hF a (chartDifference x i)
    (contDiff_chartDifference x i).contDiffOn
  exact congrArg (fun T : Module.End ℝ (SmoothSupportedTraceSection Y) => T (w i)) h

theorem smoothSupportedTraceFiberL_surjective_of_mem (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y) :
    Function.Surjective (smoothSupportedTraceFiberL (Y:=Y) x) := by
  intro u
  obtain ⟨v,hv⟩ := exists_supportedTrace_const_fiber_near hY hx u
  exact ⟨v,hv.self_of_nhds⟩

@[expose] def smoothSupportedTraceFiberDerivative
    (hY : IsOpen Y) (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (a x : X dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then
    let D := smoothSupportedTraceBaseDiff (Y:=Y) a
    let A := smoothSupportedTraceFiberAction hY F hF
    (smoothSupportedTraceFiberL (Y:=Y) x).liftOfSurjective (smoothSupportedTraceFiberL_surjective_of_mem hY hx)
      ⟨(smoothSupportedTraceFiberL x).comp (D*A-A*D),smoothSupportedTrace_baseComm_ker hY hx a F hF⟩
  else 0

theorem smoothSupportedTraceFiberDerivative_apply
    (hY : IsOpen Y) (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (a : X dim) {x : X dim} (hx : x ∈ Y)
    (u : SmoothSupportedTraceSection Y) :
    let D := smoothSupportedTraceBaseDiff (Y:=Y) a
    let A := smoothSupportedTraceFiberAction hY F hF
    smoothSupportedTraceFiberDerivative hY F hF a x (smoothSupportedTraceFiberL x u) =
      smoothSupportedTraceFiberL x ((D*A-A*D) u) := by
  simp only [smoothSupportedTraceFiberDerivative,dite_eq_left hx,LinearMap.equivOfSurjective_apply,LinearMap.comp_apply]

theorem smoothSupportedTraceFiberDerivative_regular
    (hY : IsOpen Y) (F : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (a : X dim) :
    SmoothSupportedTraceFiberRegular Y (smoothSupportedTraceFiberDerivative hY F hF a) := by
  intro u
  let D := smoothSupportedTraceBaseDiff (Y:=Y) a
  let A := smoothSupportedTraceFiberAction hY F hF
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr ((D*A-A*D) u)
  refine ⟨univ,G,isOpen_univ,subset_univ _,hG.contDiffOn,?_⟩
  intro x hx z
  rw [smoothSupportedTraceFiberDerivative_apply hY F hF a hx u,smoothSupportedTraceFiberL_apply]
  exact (hRep x z).symm

end CalderonN
