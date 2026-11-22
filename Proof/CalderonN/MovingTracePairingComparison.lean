module

public import Proof.CalderonN.MovingTraceNormIdentity
public import Mathlib.Analysis.Real.Sqrt

import Mathlib.Tactic

/-! The passage from the source commutator form to the norm of the
physical operator, on a real space carrying its positive pairing. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace CalderonN

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
  (hSym : ∀ u v, B u v = B v u) (hPos : ∀ u, 0 ≤ B u u)

include hSym hPos in
theorem sq_pairing_le_self_mul (u v : V) :
    (B u v)^2 ≤ B u u*B v v := by
  let a := B u u
  let b := B u v
  let c := B v v
  have ha : 0 ≤ a := hPos u
  have hQuad (t : ℝ) : 0 ≤ t^2*a+2*t*b+c := by
    have h := hPos (t • u+v)
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hSym v u] at h
    change 0 ≤ (t*(t*a+b)+(t*b+c)) at h
    linarith only [h]
  change b^2 ≤ a*c
  rcases ha.eq_or_lt with hZero | hPosA
  · rw [← hZero,zero_mul]
    have hb : b = 0 := by
      by_contra hne
      let t := -(c+1)/(2*b)
      have h := hQuad t
      rw [← hZero,mul_zero,zero_add] at h
      have he : 2*t*b = -(c+1) := by dsimp only [t]; field_simp <;> ring
      linarith only [h,he]
    rw [hb,zero_pow (by decide : 2 ≠ 0)]
  · have h := mul_nonneg hPosA.le (hQuad (-b/a))
    have he : a*((-b/a)^2*a+2*(-b/a)*b+c) = a*c-b^2 := by
      field_simp [hPosA.ne']
      ring
    rw [he] at h
    exact sub_nonneg.mp h

include hSym hPos in
theorem sqrt_pairing_add_le (u v : V) :
    Real.sqrt (B (u+v) (u+v)) ≤ Real.sqrt (B u u)+Real.sqrt (B v v) := by
  have hu := hPos u
  have hv := hPos v
  have hs (a : V) := Real.sq_sqrt (hPos a)
  have hxy := sq_pairing_le_self_mul B hSym hPos u v
  have hCross : B u v ≤ Real.sqrt (B u u)*Real.sqrt (B v v) := by
    calc
      _ ≤ |B u v| := le_abs_self _
      _ ≤ Real.sqrt (B u u*B v v) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hxy
      _ = _ := Real.sqrt_mul hu _
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
  rw [hs]
  simp only [map_add,LinearMap.add_apply,hSym v u]
  nlinarith only [hCross,hs u,hs v]

theorem sqrt_pairing_neg (u : V) : Real.sqrt (B (-u) (-u)) = Real.sqrt (B u u) := by
  simp only [map_neg,LinearMap.neg_apply,neg_neg]

include hSym hPos in
/-- Put (P=2T+U+J) in the manuscript's comparison, and bound the
discarded term using the same positive pairing as the output. -/
theorem movingTrace_model_comparison_of_paired_error
    (T Td L U Ud J : Module.End ℝ V) (x : V)
    (hT : ∀ u v,B (T u) v = B u (Td v)) (hU : ∀ u v,B (U u) v = B u (Ud v))
    (err : ℝ) (hErr :
      |2*B x (Td (U x)-U (Td x))+
       2*B x (Ud (T x)-T (Ud x))+
       B x (Ud (U x)-U (Ud x))-
       2*(B x (U ((L-Td) x))+B (U ((L-Td) x)) x)| ≤ err) :
    ∃ a : ℝ, 0 ≤ a ∧ 4*(B (T x) (T x)-B (L x) (L x)) ≤ a^2+err ∧
      a ≤ Real.sqrt (B ((2:ℝ) • T x+U x+J x) ((2:ℝ) • T x+U x+J x))+
        Real.sqrt (B (J x) (J x)) := by
  let v := (2:ℝ) • T x+U x
  let p := v+J x
  refine ⟨Real.sqrt (B v v),Real.sqrt_nonneg _,?_,?_⟩
  · rw [Real.sq_sqrt (hPos v)]
    exact movingTrace_model_gap_le_of_error_form B hSym hPos T Td L U Ud hT hU x err hErr
  · have h := sqrt_pairing_add_le B hSym hPos p (-J x)
    rw [show p + -J x = v by dsimp only [p]; abel,sqrt_pairing_neg B] at h
    exact h

end CalderonN
