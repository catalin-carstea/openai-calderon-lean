module

public import Proof.CalderonN.CoordinateTraceDivergence
public import Proof.CalderonN.PairedTraceFiberFamilyBounds

import Mathlib.Tactic

/-! The local bounds consumed by the quadratic forms. Only the
rank-two part of the zero coefficient needs a symbol commutator. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

structure CoordinateTraceFirstOrderBounds (A : SmoothTraceSymbolAtoms hn)
    (hY : IsOpen Y) (x : X dim) (β C : ℝ) (S : CoordinateTraceFirstOrder Y) : Prop where
  first : ∀ i,SmoothTraceSymbolBounds A 1 C ((S.first i).1 x)
  firstDerivative : ∀ i j,SmoothTraceAngularBound hn 1 (C*β) (((S.first i).derivative hY (axis j)).1 x)
  zeroDerivative : ∀ j,SmoothTraceAngularBound hn 2 (C*β^2) ((S.zero.derivative hY (axis j)).1 x)
  zeroParts : ∃ P Q : Module.End ℝ (SmoothSphereTrace dim),S.zero.1 x = P+Q ∧
    SmoothTraceSymbolBounds A 2 (C*β) P ∧ SmoothTraceAngularBound hn 1 (C*β) Q

namespace CoordinateTraceFirstOrderBounds

variable {A : SmoothTraceSymbolAtoms hn} {hY : IsOpen Y} {x : X dim} {β C : ℝ}
variable {S : CoordinateTraceFirstOrder Y}

theorem nonneg (h : CoordinateTraceFirstOrderBounds A hY x β C S) :
    0 ≤ C := (h.first 0).nonneg

theorem zero_comm (h : CoordinateTraceFirstOrderBounds A hY x β C S)
    (hβ : 0 ≤ β) {k : ℕ} {D : ℝ} {T : Module.End ℝ (SmoothSphereTrace dim)}
    (hT : SmoothTraceSymbolBounds A k D T) :
    SmoothTraceAngularBound hn (1+k) (3*(C*β*D)) (S.zero.1 x*T-T*S.zero.1 x) := by
  obtain ⟨P,Q,hEq,hP,hQ⟩ := h.zeroParts
  rw [hEq,show (P+Q)*T-T*(P+Q) = (P*T-T*P)+(Q*T-T*Q) by noncomm_ring]
  have hQT := hQ.mul hT.angular (mul_nonneg h.nonneg hβ)
  have hTQ := hT.angular.mul hQ hT.nonneg
  rw [Nat.add_comm k 1,mul_comm D (C*β)] at hTQ
  have hPt := (hP.comm hT).angular (by omega : 0 < 2+k)
  rw [show 2+k-1 = 1+k by omega] at hPt
  exact (hPt.add (hQT.sub hTQ)).enlarge (by ring_nf; rfl)

end CoordinateTraceFirstOrderBounds

structure CoordinateTraceDivergenceBounds (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y)
    (x : X dim) (β δ L : ℝ) (U : CoordinateTraceDivergence hn Y) : Prop where
  density : ∀ i,SmoothTraceAngularBound hn 0 L ((U.density i).1 x)
  second : ∀ i j,SmoothTraceAngularBound hn 0 (δ*(β⁻¹)^2) ((U.second i j).forward.1 x)
  secondDerivative : ∀ i j k,SmoothTraceAngularBound hn 0 (δ*β⁻¹)
    (((U.second i j).forward.derivative hY (axis k)).1 x)
  first : ∀ i,PairedTraceFiberFamilyBounds A hY x β 2 1 (δ*β⁻¹) (U.first i)
  zero : PairedTraceFiberFamilyBounds A hY x β 1 2 δ U.zero

end CalderonN
