module

public import Proof.CalderonN.SmoothLinearTraceMultiplierBounds

import Mathlib.Tactic

/-! Propagate angular bounds through products when commuting with
the flat degree or a coordinate rotation preserves order. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure SmoothTraceCommutatorBounds (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (order : ℕ) (C : ℝ)
    (T : Module.End ℝ (SmoothSphereTrace dim)) : Prop where
  nonneg : 0 ≤ C
  bound : SmoothTraceAngularBound hn order C T
  degree : SmoothTraceAngularBound hn order C (B*T-T*B)
  rotation : ∀ i j : I dim,SmoothTraceAngularBound hn order C (smoothTraceAngularComm i j T)

private theorem comm_right_add {R : Type*} [Ring R] (A B C : R) :
    A*(B+C)-(B+C)*A = (A*B-B*A)+(A*C-C*A) := by noncomm_ring

private theorem comm_right_sub {R : Type*} [Ring R] (A B C : R) :
    A*(B-C)-(B-C)*A = (A*B-B*A)-(A*C-C*A) := by noncomm_ring

private theorem comm_right_sum {R ι : Type*} [Ring R] (S : Finset ι) (A : R) (F : ι → R) :
    A*(∑ i ∈ S,F i)-(∑ i ∈ S,F i)*A = ∑ i ∈ S,(A*F i-F i*A) := by
  rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]

namespace SmoothTraceCommutatorBounds

variable {hn : 3 ≤ dim} {B T S : Module.End ℝ (SmoothSphereTrace dim)}
variable {k l : ℕ} {C D : ℝ}

theorem enlarge (h : SmoothTraceCommutatorBounds hn B k C T) (hCD : C ≤ D) :
    SmoothTraceCommutatorBounds hn B k D T :=
  ⟨h.nonneg.trans hCD,h.bound.enlarge hCD,h.degree.enlarge hCD,fun i j => (h.rotation i j).enlarge hCD⟩

theorem weaken (h : SmoothTraceCommutatorBounds hn B k C T) (hkl : k ≤ l) :
    SmoothTraceCommutatorBounds hn B l C T :=
  ⟨h.nonneg,h.bound.weaken h.nonneg hkl,h.degree.weaken h.nonneg hkl,
    fun i j => (h.rotation i j).weaken h.nonneg hkl⟩

theorem add (hT : SmoothTraceCommutatorBounds hn B k C T)
    (hS : SmoothTraceCommutatorBounds hn B k D S) :
    SmoothTraceCommutatorBounds hn B k (C+D) (T+S) := by
  refine ⟨add_nonneg hT.nonneg hS.nonneg,hT.bound.add hS.bound,?_,?_⟩
  · rw [comm_right_add B T S]
    exact hT.degree.add hS.degree
  · intro i j
    rw [smoothTraceAngularComm,comm_right_add (smoothSphereTraceRotation i j) T S]
    exact (hT.rotation i j).add (hS.rotation i j)

theorem sub (hT : SmoothTraceCommutatorBounds hn B k C T)
    (hS : SmoothTraceCommutatorBounds hn B k D S) :
    SmoothTraceCommutatorBounds hn B k (C+D) (T-S) := by
  refine ⟨add_nonneg hT.nonneg hS.nonneg,hT.bound.sub hS.bound,?_,?_⟩
  · rw [comm_right_sub B T S]
    exact hT.degree.sub hS.degree
  · intro i j
    rw [smoothTraceAngularComm,comm_right_sub (smoothSphereTraceRotation i j) T S]
    exact (hT.rotation i j).sub (hS.rotation i j)

theorem const_smul (hT : SmoothTraceCommutatorBounds hn B k C T) (c : ℝ) :
    SmoothTraceCommutatorBounds hn B k (|c| * C) (c • T) := by
  refine ⟨mul_nonneg (abs_nonneg _) hT.nonneg,hT.bound.const_smul c,?_,?_⟩
  · rw [mul_smul_comm c B T,smul_mul_assoc c T B,← smul_sub c (B*T) (T*B)]
    exact hT.degree.const_smul c
  · intro i j
    let R := smoothSphereTraceRotation i j
    change SmoothTraceAngularBound hn k (|c| * C) (R*(c • T)-(c • T)*R)
    rw [mul_smul_comm c R T,smul_mul_assoc c T R,← smul_sub c (R*T) (T*R)]
    exact (hT.rotation i j).const_smul c

theorem mul (hT : SmoothTraceCommutatorBounds hn B k C T)
    (hS : SmoothTraceCommutatorBounds hn B l D S) :
    SmoothTraceCommutatorBounds hn B (k+l) (C*D+C*D) (T*S) := by
  have hPos := mul_nonneg hT.nonneg hS.nonneg
  refine ⟨add_nonneg hPos hPos,(hT.bound.mul hS.bound hT.nonneg).enlarge (le_add_of_nonneg_right hPos),?_,?_⟩
  · exact hT.bound.comm_mul_right hS.bound hT.degree hS.degree rfl hT.nonneg hT.nonneg
  · intro i j
    exact hT.bound.comm_mul_right hS.bound (hT.rotation i j) (hS.rotation i j) rfl hT.nonneg hT.nonneg

theorem sum {ι : Type*} (t : Finset ι) (T : ι → Module.End ℝ (SmoothSphereTrace dim))
    (C : ι → ℝ) (h : ∀ i ∈ t,SmoothTraceCommutatorBounds hn B k (C i) (T i)) :
    SmoothTraceCommutatorBounds hn B k (∑ i ∈ t,C i) (∑ i ∈ t,T i) := by
  refine ⟨Finset.sum_nonneg (fun i hi => (h i hi).nonneg),
    SmoothTraceAngularBound.sum t T C (fun i hi => (h i hi).bound),?_,?_⟩
  · rw [comm_right_sum t B T]
    exact SmoothTraceAngularBound.sum t _ C (fun i hi => (h i hi).degree)
  · intro a b
    rw [smoothTraceAngularComm,comm_right_sum t (smoothSphereTraceRotation a b) T]
    exact SmoothTraceAngularBound.sum t _ C (fun i hi => (h i hi).rotation a b)

end SmoothTraceCommutatorBounds

end CalderonN
