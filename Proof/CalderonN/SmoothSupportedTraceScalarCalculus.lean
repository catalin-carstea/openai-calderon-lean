module

public import Proof.CalderonN.SmoothSupportedTraceBaseCommutation

import Mathlib.Tactic

/-! Scalar multipliers and the ordinary coordinate product rule on the
smooth compactly supported trace domain. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hY : IsOpen Y)

theorem smoothSupportedTraceBaseMul_congr {f g : X dim → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) (h : EqOn f g Y) :
    smoothSupportedTraceBaseMul hY f hf = smoothSupportedTraceBaseMul hY g hg := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  rw [smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceBaseMul_fiber,h hx]

theorem smoothSupportedTraceBaseMul_mul (f g : X dim → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) :
    smoothSupportedTraceBaseMul hY (fun x => f x*g x) (hf.mul hg) =
      smoothSupportedTraceBaseMul hY f hf*smoothSupportedTraceBaseMul hY g hg := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,smul_smul]

theorem smoothSupportedTraceBaseMul_add (f g : X dim → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) :
    smoothSupportedTraceBaseMul hY (fun x => f x+g x) (hf.add hg) =
      smoothSupportedTraceBaseMul hY f hf+smoothSupportedTraceBaseMul hY g hg := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [LinearMap.add_apply,map_add,smoothSupportedTraceBaseMul_fiber,add_smul]

theorem smoothSupportedTraceBaseMul_neg (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    smoothSupportedTraceBaseMul hY (fun x => -f x) hf.neg = -smoothSupportedTraceBaseMul hY f hf := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [LinearMap.neg_apply,map_neg,smoothSupportedTraceBaseMul_fiber]
  exact neg_smul (f x) (smoothSupportedTraceFiberL x u)

theorem smoothSupportedTraceBaseMul_sum {ι : Type*} (s : Finset ι)
    (f : ι → X dim → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Y) :
    smoothSupportedTraceBaseMul hY (fun x => ∑ i ∈ s,f i x) (ContDiffOn.sum (fun i _ => hf i)) =
      ∑ i ∈ s,smoothSupportedTraceBaseMul hY (f i) (hf i) := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [LinearMap.sum_apply,map_sum,smoothSupportedTraceBaseMul_fiber,Finset.sum_smul]

theorem smoothSupportedTraceBaseMul_comm_fiber (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y)
    (T : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hT : SmoothSupportedTraceFiberRegular Y T) :
    smoothSupportedTraceBaseMul hY f hf*smoothSupportedTraceFiberAction hY T hT =
      smoothSupportedTraceFiberAction hY T hT*smoothSupportedTraceBaseMul hY f hf := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x _
  simp only [Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceFiberAction_fiber,map_smul]

theorem smoothSupportedTraceBaseDiff_mul (a : X dim) (f : X dim → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y) :
    let f' (x : X dim) := fderiv ℝ f x a
    let hf' : ContDiffOn ℝ ∞ f' Y := (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
    smoothSupportedTraceBaseDiff a*smoothSupportedTraceBaseMul hY f hf =
      smoothSupportedTraceBaseMul hY f hf*smoothSupportedTraceBaseDiff a+
        smoothSupportedTraceBaseMul hY f' hf' := by
  dsimp only
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  apply Subtype.ext
  funext z
  simp only [smoothSupportedTraceFiberL_apply,Module.End.mul_apply,LinearMap.add_apply,Submodule.coe_add,Pi.add_apply,
    supportedTraceBaseMul_apply,smoothSupportedTraceBaseDiff_apply,standardTraceBaseDiff]
  have hD : DifferentiableAt ℝ f x := (hf.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
  have hU : DifferentiableAt ℝ (fun y => u.1 (y,z)) x := by
    rw [show (fun y => u.1 (y,z)) = fun y => G (y,(z:X dim)) from funext (fun y => hRep y z)]
    exact (hG.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x
  rw [fderiv_fun_mul hD hU]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

end CalderonN
