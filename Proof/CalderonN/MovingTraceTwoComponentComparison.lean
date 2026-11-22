module

public import Proof.CalderonN.MovingTracePairingComparison
public import Mathlib.LinearAlgebra.Prod

import Mathlib.Tactic

/-! Apply the real moving trace comparison simultaneously to the real and
imaginary components, using their sum pairing. -/

public section

noncomputable section
set_option autoImplicit false
namespace CalderonN

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

@[expose] def movingTraceAdjointErrorForm (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T Td L U Ud : Module.End ℝ V) (x : V) : ℝ :=
  2*B x (Td (U x)-U (Td x))+
    2*B x (Ud (T x)-T (Ud x))+
    B x (Ud (U x)-U (Ud x))-
    2*(B x (U ((L-Td) x))+B (U ((L-Td) x)) x)

private def sumPairing (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : (V × V) →ₗ[ℝ] (V × V) →ₗ[ℝ] ℝ where
  toFun u := (B u.1).comp (LinearMap.fst ℝ V V)+(B u.2).comp (LinearMap.snd ℝ V V)
  map_add' u v := by
    apply LinearMap.ext
    intro w
    simp only [Prod.fst_add,Prod.snd_add,map_add,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.fst_apply,LinearMap.snd_apply]
    abel
  map_smul' a u := by
    apply LinearMap.ext
    intro w
    change ((B (a • u.1)).comp (LinearMap.fst ℝ V V)+(B (a • u.2)).comp (LinearMap.snd ℝ V V)) w =
      (a • ((B u.1).comp (LinearMap.fst ℝ V V)+(B u.2).comp (LinearMap.snd ℝ V V))) w
    simp only [map_smul,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.fst_apply,LinearMap.snd_apply,LinearMap.smul_apply,smul_eq_mul,mul_add]

@[simp] private theorem sumPairing_apply (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v : V × V) :
    sumPairing B u v = B u.1 v.1+B u.2 v.2 := rfl

theorem sqrt_twoComponent_pairing_add_le
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hSym : ∀ u v,B u v = B v u) (hPos : ∀ u,0 ≤ B u u)
    (u v w z : V) :
    Real.sqrt (B (u+w) (u+w)+B (v+z) (v+z)) ≤
      Real.sqrt (B u u+B v v)+Real.sqrt (B w w+B z z) := by
  let B₂ := sumPairing B
  have hSym₂ (p q : V × V) : B₂ p q = B₂ q p := by
    simp only [B₂,sumPairing_apply,hSym p.1 q.1,hSym p.2 q.2]
  have hPos₂ (p : V × V) : 0 ≤ B₂ p p := add_nonneg (hPos p.1) (hPos p.2)
  exact sqrt_pairing_add_le B₂ hSym₂ hPos₂ (u,v) (w,z)

theorem movingTrace_twoComponent_comparison
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hSym : ∀ u v,B u v = B v u) (hPos : ∀ u,0 ≤ B u u)
    (P T Td L U Ud J : Module.End ℝ V) (hP : P = (2:ℝ) • T+U+J) (x y : V)
    (hT : ∀ u v,B (T u) v = B u (Td v)) (hU : ∀ u v,B (U u) v = B u (Ud v))
    (e j : ℝ)
    (hE : |movingTraceAdjointErrorForm B T Td L U Ud x+
      movingTraceAdjointErrorForm B T Td L U Ud y| ≤ e)
    (hJ : Real.sqrt (B (J x) (J x)+B (J y) (J y)) ≤ j) :
    ∃ a : ℝ, 0 ≤ a ∧
      4*((B (T x) (T x)+B (T y) (T y))-(B (L x) (L x)+B (L y) (L y))) ≤ a^2+e ∧
      a ≤ Real.sqrt (B (P x) (P x)+B (P y) (P y))+j := by
  let B₂ := sumPairing B
  let lift (A : Module.End ℝ V) : Module.End ℝ (V × V) := A.prodMap A
  have hSym₂ (u v : V × V) : B₂ u v = B₂ v u := by
    simp only [B₂,sumPairing_apply,hSym u.1 v.1,hSym u.2 v.2]
  have hPos₂ (u : V × V) : 0 ≤ B₂ u u := add_nonneg (hPos u.1) (hPos u.2)
  have hT₂ (u v : V × V) : B₂ (lift T u) v = B₂ u (lift Td v) := by
    simp only [B₂,lift,sumPairing_apply,LinearMap.prodMap_apply,hT]
  have hU₂ (u v : V × V) : B₂ (lift U u) v = B₂ u (lift Ud v) := by
    simp only [B₂,lift,sumPairing_apply,LinearMap.prodMap_apply,hU]
  have hE₂ : movingTraceAdjointErrorForm B₂ (lift T) (lift Td) (lift L) (lift U) (lift Ud) (x,y) =
      movingTraceAdjointErrorForm B T Td L U Ud x+movingTraceAdjointErrorForm B T Td L U Ud y := by
    simp only [movingTraceAdjointErrorForm,B₂,lift,sumPairing_apply,LinearMap.prodMap_apply,
      LinearMap.sub_apply,Prod.fst_sub,Prod.snd_sub]
    ring
  have hE₂' : |movingTraceAdjointErrorForm B₂ (lift T) (lift Td) (lift L) (lift U) (lift Ud) (x,y)| ≤ e := by
    rw [hE₂]
    exact hE
  obtain ⟨a,ha,hGap,hNorm⟩ := movingTrace_model_comparison_of_paired_error B₂ hSym₂ hPos₂
    (lift T) (lift Td) (lift L) (lift U) (lift Ud) (lift J) (x,y) hT₂ hU₂
    e hE₂'
  change 4*((B (T x) (T x)+B (T y) (T y))-(B (L x) (L x)+B (L y) (L y))) ≤ a^2+e at hGap
  refine ⟨a,ha,hGap,hNorm.trans ?_⟩
  rw [hP]
  apply add_le_add _ hJ
  rfl

end CalderonN
