module

public import Proof.CalderonN.TraceCoordinateFiberCommutator

import Mathlib.Tactic

/-! Fiber estimates for supported operators, including their
angular adjoints on the common smooth trace core. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

@[expose] def SupportedTraceFiberBound (hn : 3 ≤ dim) (x : X dim) (order : ℕ) (C : ℝ)
    (J : Module.End ℝ (SmoothSupportedTraceSection Y)) : Prop :=
  ∃ A A' : Module.End ℝ (SmoothSphereTrace dim), SmoothTraceAdjoint hn A A' ∧
    SmoothTraceAngularBound hn order C A ∧
    ∀ u,smoothSupportedTraceFiberL x (J u) = A (smoothSupportedTraceFiberL x u)

namespace SupportedTraceFiberBound
variable {hn : 3 ≤ dim} {x : X dim} {k l : ℕ} {C D : ℝ}
variable {A B : Module.End ℝ (SmoothSupportedTraceSection Y)}

theorem enlarge (hA : SupportedTraceFiberBound hn x k C A) (hCD : C ≤ D) :
    SupportedTraceFiberBound hn x k D A := by
  obtain ⟨U,V,hUV,hU,h⟩ := hA
  exact ⟨U,V,hUV,hU.enlarge hCD,h⟩

theorem add (hA : SupportedTraceFiberBound hn x k C A) (hB : SupportedTraceFiberBound hn x k D B) :
    SupportedTraceFiberBound hn x k (C+D) (A+B) := by
  obtain ⟨U,U',hU,h₁,hA⟩ := hA
  obtain ⟨V,V',hV,h₂,hB⟩ := hB
  exact ⟨U+V,U'+V',hU.add hV,h₁.add h₂,fun u => by
    simp only [LinearMap.add_apply,map_add,hA,hB]⟩

theorem mul (hA : SupportedTraceFiberBound hn x k C A) (hB : SupportedTraceFiberBound hn x l D B)
    (hC : 0 ≤ C) : SupportedTraceFiberBound hn x (k+l) (C*D) (A*B) := by
  obtain ⟨U,U',hU,h₁,hA⟩ := hA
  obtain ⟨V,V',hV,h₂,hB⟩ := hB
  exact ⟨U*V,V'*U',hU.mul hV,h₁.mul h₂ hC,fun u => by simp only [Module.End.mul_apply,hA,hB]⟩

theorem base_mul (hA : SupportedTraceFiberBound hn x k C A) (hY : IsOpen Y)
    (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y) :
    SupportedTraceFiberBound hn x k (|f x| * C) (smoothSupportedTraceBaseMul hY f hf*A) := by
  obtain ⟨U,U',hU,h₁,hA⟩ := hA
  exact ⟨f x • U,f x • U',hU.const_smul _,h₁.const_smul _,fun u => by
    simp only [Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,hA,LinearMap.smul_apply]⟩

theorem sum {ι : Type*} (t : Finset ι) (T : ι → Module.End ℝ (SmoothSupportedTraceSection Y))
    (C : ι → ℝ) (h : ∀ i ∈ t,SupportedTraceFiberBound hn x k (C i) (T i)) :
    SupportedTraceFiberBound hn x k (∑ i ∈ t,C i) (∑ i ∈ t,T i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨0,0,?_,?_,?_⟩
    · intro u v
      simp only [LinearMap.zero_apply,map_zero,inner_zero_left,inner_zero_right]
    · intro i j _ u
      simp only [LinearMap.zero_apply,traceOrderNorm,map_zero,norm_zero,zero_mul,le_rfl]
    · intro u
      simp only [LinearMap.zero_apply,map_zero]
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end SupportedTraceFiberBound

end CalderonN
