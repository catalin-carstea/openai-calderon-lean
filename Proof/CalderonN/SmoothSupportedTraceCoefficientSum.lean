module

public import Proof.CalderonN.TraceCoordinateModelCommBounds

import Mathlib.Tactic

/-! Finite contractions preserve the first chart derivative bounds. -/

public section

noncomputable section
open Set
open scoped ContDiff Topology Classical
set_option autoImplicit false
set_option maxHeartbeats 3100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceFiberRegular_zero :
    SmoothSupportedTraceFiberRegular Y (fun _ => (0 : Module.End ℝ (SmoothSphereTrace dim))) := by
  intro u
  refine ⟨univ,0,isOpen_univ,subset_univ _,contDiffOn_const,fun _ _ _ => rfl⟩

theorem SmoothSupportedTraceCoefficientBounds.finite_sum
    {hn : 3 ≤ dim} {B : Module.End ℝ (SmoothSphereTrace dim)} {hY : IsOpen Y} {x : X dim}
    {β : ℝ} (hβ : 0 ≤ β) (hx : x ∈ Y) {k : ℕ} {ι : Type*} (t : Finset ι)
    (F : ι → X dim → Module.End ℝ (SmoothSphereTrace dim))
    (C : ι → ℝ) (hF : ∀ i ∈ t,SmoothSupportedTraceFiberRegular Y (F i))
    (h : ∀ i (hi : i ∈ t),SmoothSupportedTraceCoefficientBounds hn B hY x β k (C i) (F i) (hF i hi)) :
    SmoothSupportedTraceCoefficientBounds hn B hY x β k (∑ i ∈ t,C i)
      (fun x => ∑ i ∈ t,F i x) (SmoothSupportedTraceFiberRegular.sum t F hF) := by
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have hZero : SmoothTraceAngularBound hn k 0 (0 : Module.End ℝ (SmoothSphereTrace dim)) := by
      intro i j hij u
      simp only [LinearMap.zero_apply,traceOrderNorm,map_zero,norm_zero,zero_mul,le_rfl]
    have hB₀ : SmoothTraceCommutatorBounds hn B k 0 (0 : Module.End ℝ (SmoothSphereTrace dim)) := by
      refine ⟨le_rfl,hZero,?_,?_⟩
      · intro i j hij u
        simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.zero_apply,map_zero,sub_zero,
          traceOrderNorm,norm_zero,zero_mul,le_rfl]
      · intro a b i j hij u
        simp only [smoothTraceAngularComm,LinearMap.sub_apply,Module.End.mul_apply,LinearMap.zero_apply,
          map_zero,sub_zero,traceOrderNorm,norm_zero,zero_mul,le_rfl]
    exact SmoothSupportedTraceCoefficientBounds.const hB₀ hx hβ
  | @insert i t hit ih =>
    have hF₀ k (hk : k ∈ t) := hF k (Finset.mem_insert_of_mem hk)
    have hi := h i (Finset.mem_insert_self _ _)
    have hRest := ih hF₀ (fun k hk => h k (Finset.mem_insert_of_mem hk))
    have hCoeff := hi.add hRest hx
    have he : (fun x => F i x+∑ k ∈ t,F k x) = fun x => ∑ k ∈ insert i t,F k x := by
      funext x
      rw [Finset.sum_insert hit]
    rw [Finset.sum_insert hit]
    exact hCoeff.congr hx (he ▸ Filter.EventuallyEq.rfl)

end CalderonN
